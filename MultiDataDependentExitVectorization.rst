-------------------------------------------------
MultiExit Loop Vectorization
-------------------------------------------------

Vectorization of loops with multiple exits has always been an attractive but challenging task. The last attempt to improve the situation with handling multi-exit loops in general and data-dependent exit loops in particular was taken by Philip several years ago. Here is a corresponding discussion on llvm-dev list https://lists.llvm.org/pipermail/llvm-dev/2019-September/134998.html and Philip’s notes on github https://github.com/preames/public-notes/blob/master/multiple-exit-vectorization.rst. The goal of this write-up is to kick-off a discussion which should finally define our vision and achieve progress in this critical but difficult task.

This document is divided into three sections: First, we discuss the general approach to support vectorization when we have data dependent exits, including the formulae for predicates, legality constraints and the cost model. We go through this same discussion in the second part where we identify a simpler approach compared to the general one. Finally, in the very last section, we discuss how we could reduce this simpler approach to just a stand-alone pass run before the loop vectorizer.   

.. contents::

Background
------------

The loop vectorizer currently handles single exit loops, where the exit is from the latch. If we have early exits from the loop, then we cannot vectorize the loop. Here is an example, we currently vectorize. 

.. code::

   int i = 0;
   if (i < N) {
     do {
      a[i] = i;
      i++;
    } while (i < N);
  }

This is the lowered form of a `for(int i = 0; i < N; i++)` loop.  There are a couple of key things to notice:

* It has a bottom tested exit condition.  This means that only the latch block exits the loop.
* It has a loop guard before the loop which ensures the exit condition is true on initial entry to the loop.
* Because the sole exit is also the loop latch (the source of the backedge), all instructions within the loop execute an equal number of times.

In addition, the loop vectorizer has support for internal predication.  That is, the body of the loop can contain instructions which execute conditionally.


There are two kinds of early exits from the loop:

* A regular early exit where there is no dependence of value loaded from memory. For example, an exit condition like `if (i > M) break;`. Typically, such conditions should have already been removed by either fusing with the latch termination condition above `while(i < N)`. These are not as interesting, since we have ways to handle this through earlier optimizations.
* A data dependent early exit where the condition involves loading from memory and performing some check. For example, `if (a[i] == X) break`. Here, the most important legality constraint we need to prove irrespective of how we choose to vectorize, is that in the vectorized form, we do not load from unmapped memory. 


Introduction
--------------

There are three key differences that need to be considered when we support multi exit loop vectorization. 

The first difference is that in addition to explicit conditions, instruction execution becomes dependent on all preceding (at runtime) conditions guarding dd-exits. That is, in the first case (normal loop vectorization), instructions that are not explicitly guarded will be unconditionally executed for each lane in the vector code. While in the data-dependent exit case, the instructions should not be executed for already exited lanes. That means execution becomes dependent on all conditions guarding dd-exits. Moreover, that effectively means it should be safe to evaluate all such conditions upfront even though some of them may not be evaluated at all in the scalar execution. This introduces additional legality constrains we need to consider. 


The second difference is how live outs are calculated. In the first case, live out value is simply extracted from the last lane of the final vector iteration. While in the second case, it should be extracted from the last lane active at the definition(s) of these live outs. 

The third difference is in how to accurately compute the cost of vectorization, i.e. the cost modelling.

For the convenience of further reading, we introduce some acronyms and notations: 
 
VF – number of lanes in vector execution and assumed to be 4 through this document 

^ - vector notation where lanes are numbered starting from 1 and ordered from left to right. For example, X^ means vector of [X1, … XVF] 

~ - negation, for example ~X is negation of X 

C1,  ..., CN – loop exiting conditions 

I0,  ..., IN – any other instruction but C1,  ..., CN 

P0, …PN – corresponding predicates for I0,  ..., IN 

CLSZ(X^) - counts number of least significant zeros in vector X^ (from left to right) 

CLSNZ(X^) - counts number of least significant non zeros in vector X^ (from left to right) 

Extract(X^, n) – extract nth lane from vector X^, where vector lanes are numbered 1,2,3,..,VF  
 


General Model
--------------

We now dive into how vectorization will look like when we have multiple exits throughout the loop. 


Predication
============

As it was mentioned vectorization of loops with dd-exits assumes dealing with possibility of exiting the loop in the middle of iteration. That is, all instructions within the loop following taken exit at runtime should not be executed.  It’s important to understand that any instruction (even the very first) of the next iteration follows at runtime all dd-exiting guards of the previous iteration. Most natural way for the vectorizer to achieve conditional execution is through the predication. Let’s see what predicates should look like using the following example:

.. _predication_example:

.. code::

   i = 0;
   if (i < N) {
     do {
       I0;
       if(C1) {
         I1;
         break;
       }
       I2;
       i++;
     } while (i < N);
   }

Let’s also assume C1 is 0 for the first iteration and 1 for the second one. Please note that C1 is not evaluated for the remaining iterations in scalar execution thus effectively making it ‘undef’. Now let’s see what values predicates should take if we want to execute it in vector form: 

.. code::

   for(i=0; I < N; ++i) {
     P0:=[1,1,0,0]: I0;
     P1:=[0,1,0,0]: I1; 
     P2:=[1,0,0,0]: I2; 
   }


Here are the formulas to calculate predicates (details can be provided if needed):

P0^ = 2 :sup:`CLSZ(C1^)+1` – 1 == 2 :sup:`CLSZ([0,1,undef,undef])+1`-1 == 2 :sup:`1+1`-1 == 3 = [1, 1, 0, 0]
 
P1^ = P0^ & C1^ == [1, 1,  0, 0] & [0, 1, undef, undef] == [0, 1, 0, 0]

P2^ = P0^ & ~C1^ == [1, 1,  0, 0] & [1, 0, undef, undef] == [1, 0, 0, 0]


That is, P0 gives active vector lanes at the beginning of vector iteration, while P2 at the end. So, to get semantically equal execution to the scalar code, the  instructions should be executed under corresponding predicates. However, there is one big caveat. Predicate for I0 depends on C1. That means it should be valid to do two things:
 
 1.  Evaluate C1 before I0 without breaking program semantics. 
 2.  Evaluate C1 for lanes not evaluated in scalar execution. 

We refer to these two properties as “hoistability” and “speculatability” respectively throughout the document and will be discussed in detail later.

It’s not hard to see (proof by induction: details can be provided if needed) how formulas are generalized to an arbitrary number ‘k’ of early exits:

P :sub:`0` :sup:`LOOP` = 2 :sup:`CLSZ(C1^|…| Ck^)+1` – 1

P :sub:`i` :sup:`LOOP` = P0 & ~(C1^| … | Ci^), for i > 0 && i <= k

P :sub:`i` :sup:`EXIT` = P0 & Ci & ~(C1^| … | Ci-1^), for i > 0 && i <= k

P :sub:`0` :sup:`LOOP` is a predicate for instructions preceding the first dd-exit. P :sub:`i` :sup:`LOOP` is a predicate for instructions contained in the loop, which dominate the latch, where C1^, …, Ci^ are early exits dominating the instruction. P :sub:`i` :sup:`EXIT` is a predicate for instructions belonging to loop exiting blocks (I.e. these instructions do not dominate the loop latch), where Ci is the exiting condition. In case of nested conditions, resulting condition should be formed by ‘and’ing all enclosing conditions.

Hoistability
============
 
As we already know, vector instructions should be executed under corresponding predicates that depend on ALL conditions guarding dd-exits. That means we should hoist all such conditions (and their definitions) to the very beginning.  Of course, such hoisting should not break semantic correctness. Let’s give formal definition of hoisting safety: 

Hoisting Safety
  We say it’s safe to hoist instruction to an earlier point in the execution if it produces the same result as in the original execution and early result availability doesn’t cause observable change in the program behavior. 

Typical examples of unsafe instruction hoisting are moving a load ahead of potentially aliasing store or scheduling potentially throwing instruction ahead of another side-effecting instruction. In LLVM terms, this is very similar to ``llvm::canSinkOrHoistInst`` used in LICM along with avoiding hoisting over instructions that fail ``isGuaranteedToTransferExecutionToSuccessor`` (for example, may Throw calls or returns). Note that we can still hoist over throwing calls if we prove the instruction we are hoisting is speculatable (see below). 

Speculatability
===============

Hoisting safety is required but not enough to guarantee vectorization correctness. In addition, it should be safe to evaluate dd-exiting conditions for iterations potentially not executed in the scalar loop. In the scalar loop, dd-exiting conditions may be explicitly guarded by other dominating conditions as well as implicitly by exiting conditions from the previous iteration(s). So, in the vectorized form, it should be safe to evaluate such conditions speculatively. Here is the formal definition(s): 

Speculated
  An instruction is speculatively executed (or speculated) when it is executed in the modified program while it potentially may not be executed in the original program. 

Safe Speculation
  We say that speculative execution is safe if it does not introduce new undefined behaviours.  

One intuitive way to this about this is to take the scalar loop with the data dependent exits and unroll it `VF` times. The first step is we check hoisting safety for all these data dependent exits (from the unrolled iterations) to the start of the loop. Then, we check if these instructions being hoisted are ``isSafeToSpeculativelyExecute`` with the ``ContextInstruction`` being the point it is hoisted to. 

An obvious candidate for proving speculation safety are loads from memory. This is because with multi-exit loop vectorization, we can now perform loads from memory that will cause undefined behaviour if we try to read from memory that is not derefenceable. Other examples where we need to prove speculation safety is if we load or introduce a poison value in the vectorized code and cause immediate UB (by using that poison value), while in the scalar form, we exited the loop before the use of poison. For example, adding two values where we have NoWrapFlags. If in the vectorized form, we speculatively execute this add and we wrap-around, the result of the add is a poison value. If we end up branching on that poison value, we introduce undefined behaviour (UB).  

We make a distinction between immediate undefined behaviour and deferred UB. In speculation, immediate UB (loading non-dereferenceable memory or a div-by-0) should be identified and we should bail out of vectorization. However, deferred UB is poison and is handled through `freeze`.

Let us consider several examples to better understand what “speculation safety” means.  We start with a classical search loop example but written in a bottom tested form (which is the form expected in loop vectorizer): 


.. code::

  i = 0;
  if ( i < N) {
   do {
    char x = a[i];
    bool c = (x == 0);
    if (c) break;
    foo(x);
    ++i;
   } while (i < N);
  }

This loop has a single dd-exit guarded by condition ‘c’.  Let’s for simplicity assume array ‘a’ has byte-wide elements with first zero element at position M = N/2, where N mod 2. This way scalar loop will not access anything beyond a[M]. To vectorize this loop it should be safe to evaluate ‘a[i]’ for up to VF bytes beyond memory read on previous vector iteration. Thus, it should be valid to dereference up to VF bytes beyond that accessed in scalar execution. Fortunately, there is another condition “!(0 <= i < N)” guaranteeing vector loop will not try to load more than N bytes from the start of ‘a’ (assuming “VF mod 2” && VF <= N). Thus, it is enough to prove there is N bytes dereferenceable from start of ‘a’.

In addition to dereferenceability aspect, poison values may appear as a result of speculative reads. Since these speculatively read values are used as a branch condition later it can produce undefined behavior. This means each speculatively evaluated condition should be ‘frozen’.  To prove the legality of “freezing” it’s enough to show that predicates do not change after freezing. Here is how frozen predicates look like:

P :sub:`0` :sup:`LOOP` = 2 :sup:`CLSZ(freeze(C1^)|…| freeze(Cn^))+1` – 1

P :sub:`i` :sup:`LOOP` = P0 & ~(freeze(C1^)| … | freeze(Ci^)), for i > 0

P :sub:`i` :sup:`EXIT` = P0 & Ci & ~(freeze(C1^)| … | freeze(Ci-1^)), for i > 0 

If loaded value is poison, ‘freeze’ of that value can be replaced with ‘undef’. Otherwise, it is any value in the given type that is semantically equal to ‘undef’ as well. Thus, we can model speculatively loaded values with ‘undef’. Let’s assume we take exit ‘k’ on iteration ‘m’. Thus dd-exit conditions have the following values after freezing:
 
Ci = [0 :sub:`1`, …0 :sub:`m-1`, 0 :sub:`m`,         undef :sub:`m+1`, …, undef :sub:`n` ], for i < k

Ci = [0 :sub:`1`, …0 :sub:`m-1`, 1 :sub:`m`,         undef :sub:`m+1` , …, undef :sub:`n` ], for i == k

Ci = [0 :sub:`1`, …0 :sub:`m-1`, undef :sub:`m` , undef :sub:`m+1`, …, undef :sub:`n` ], for i > k

This means ``C0 | … | Cm`` == ``freeze(C0) | … | freeze(Cm)``. Thus ``CLSZ(C1^|…| Cn^)`` == ``CLSZ(freeze(C1^)|…| freeze(Cn^))``.

So P :sub:`0` :sup:`LOOP` doesn’t change after freezing. Since P :sub:`0` :sup:`LOOP` hasn’t changed, it’s easy to see that P :sub:`I` :sup:`LOOP` and P :sub:`I` :sup:`EXIT` do not change either.

Summarizing we end up with the following vector loop (we avoid showing the scalar post loop for convenience):


.. code::

  i = 0;
  if ( i < N) {
   do {
    char x^ = a^;
    char x1^ = freeze(x^)
    bool c^ = (x1^ == 0^);
    if (anyof(c^)) break;
    foo^(x^);
    i += VF;
   } while ( i < N);
  }

Let us consider a bit more complicated example involving indirect memory access:

.. code::

  while(true) {
    int x = a[i];
    bool c1 = (0 <=x < K);
    if (c1) break;
    foo(x);
    char y = b[x];
    bool c2 = (y == 0);
    if (c2) break;
    bar(y);
    ++i;
    if (!(0 <= i < N)) break;
  }

In this example, the first early exit guarded by c1 provides safety of indirect access b[x]. As before, it’s required to prove safety of speculative evaluation of c1 and c2. For c1 the same reasoning as for the previous example works. For c2, things are a bit more interesting. Again, to prove safety of c2 speculative evaluation it’s required to prove dereferenceability of b[x], where “frozen” value of x is used (because ‘x’ is also evaluated speculatively). Since freezing of potentially poison value is essentially ‘undef’ value it is impossible to prove dereferenceability of b[x] (without additional tricks which are explained later).

Let us consider a case which requires speculation of potentially faulting instruction. For example, integer division:


.. code::

  while(true) {
    int x = a[i];
    int y = b[i];
    int z = x/y;
    bool c1 = (z == 1);
    if (c1) break;
    foo(x);
    ++i;
    if (!(0 <= i < N)) break;
  }

It may seem that it’s safe to vectorize such a loop but it’s not. Even though ‘x/y’ is not explicitly guarded in scalar execution its execution still depends on exits following it. Thus, vectorization involves speculation of ‘x/y’ and will immediately produce a fault if speculatively read value (b[i]) appears to be 0. That is, assuming a[0] == b[0] != 0, scalar loop will execute exactly one iteration and exit. If at the same time b[1] == 0, then speculative evaluation of x^/y^ required for vectorization will produce a fault making such vectorization illegal. Such cases of  immediately introducing UB should be identified and bailed out. 

Finally, let us consider the case similar as above, but this time, we have a div-by-0 check:

.. code::

  while(true) {
    int x = a[i];
    int y = b[i];
    if (y == 0) break;  // Condition C0
    int z = x/y;
    bool c1 = (z == 1); // Condition C1
    if (c1) break;
    foo(x);
    ++i;
    if (!(0 <= i < N)) break;
  }

Here we have an instruction that causes UB between both the conditions C0 and C1. We can successfully vectorize C0 if we prove that load of array `b` can be safely speculated upto `N` iterations. However, C1 is guarded by C0. To consider speculation of C1 safe, we need to prove it is safe at the context being the start of the loop. 


Cost modelling
==============

Cost modelling is an easy and hard task at the same time. On the one hand, it’s easy because existing implementation can already handle predicated execution and dd-exit vectorization case seems to be well covered by that. Special handling will be needed for cost estimation of dd-exit conditions that are hoisted and speculatively evaluated for entire lane in the vector execution while they can be conditionally evaluated in the scalar execution. 
On the other hand, it’s hard to accurately predict the real number of iterations in the loop since each dd-exit can exit the loop (I.e. it may run much lower than estimated number of iterations).  
 

Live outs 
==========

The possibility of exiting a loop in the middle of the execution makes it challenging to find out live out values. In case when there are no exits that can break loop’s execution, last scalar iteration maps to the last lane of the last vector iteration. Thus, the live out value can be simply extracted from the last lane right after the vector loop. In the case of presence of dd-exits things are more complicated. Live out value should be extracted from the last lane active at the live out definition. That means two things. First, the last value extraction mask is a disjunction of Pi predicates (gives active vector lanes) under which live out is defined. Second, the last value extraction mask is individual for each live out. Let us try understanding things using the following example: 


.. code::

  X = 0;
  for (i=0; I < N; ++i) {
    if(C1) {
      break;
    }   
    X = A[i];
  }
  print(X);

Here `X` is a live out. Let us, as in the previous example, assume C1 is 0 for the first iteration and 1 for the second one. Then live out value should be A[0] meaning it should be extracted from the 1st lane (out of the 4 lanes in the vector). Since predicate corresponding to `X = A[i]` instruction is P2 we end up with the following extraction mask:

EMask(X) = P2^:= P0^ & ~C1^ = [1, 0, 0, 0]

Corresponding live out value should be extracted from the last active lane given by the mask:

X = Extract(X^, CLSNZ(EMask(X))) = Extract(X^,  1) = A[0] as expected.

Let us modify previous example so that live out is re-defined at dd-exit block itself:


.. code::

  X = 0;
  for (i=0; I < N; ++i) {
    if(C1) {
      X = B[i];
      break;
    }
    X = A[i];
  }
  print(X);

Under all the same assumptions as used for the above example, ‘X’ is equal to B[1] after the loop. Let us form a last value extraction mask:

EMask(X) = (P1|P2) = (P0^ & C1^)|(P0^ & ~C1^) = P0= [1, 1, 0, 0]

X = Extract(X^, CLSNZ(EMask(X))) = Extract([A[0], B[1], “undef”, “undef”],  2) = B[1] as expected.

Thus, to generalize, last value extraction mask for live out X:

EMask(X) = (Pi | … | Pj), where Pi are predicates under which X is defined.



The Simple Approach
--------------------

Well, vectorization of loops with dd-exits is challenging task because the loop can be exited from the middle. But what if we make vector code to execute all iterations but the last one where the loop is exited? In other words, we can copy original loop and rewrite it in the form where all original dd-exits are replaced with a single test placed at the very beginning of the loop. If the test passes, continue with the loop body otherwise fall back to the original scalar loop with dd-exits. Let’s see how the described transformation looks like on the predication_example_ from above :

.. code::

  i=0;
  if ( i < N) {
    // Scalar loop which will be vectorized. We have moved all early exits to the start of the loop.
    do {
      if (C1) {
         break;
      }
      I0;
      I1;
      I2;
      I++;
    } while ( i < N);

    // Scalar post loop for executing the remaining iterations when we exit the above loop.
    for(j = i; j < N; ++j) {
      I0;
      if (C1) {
        I1;
        break;
      }
      I2;
    }
  }
 
So, we effectively converted our task of vectorization of a loop with dd-exits into vectorization of a loop with single early dd-exit. Moreover, this single exit can now be “widened” (by analogies of guard widening) since it’s always valid to fall back to the original loop. Let’s see what it takes to vectorize the loop in this form.

Simple Approach Predication
===========================

Let’s see how predicates change under C1^| … | Cn^ == 0 assumption:
	
P :sub:`0`  = 2 :sup:`CLSZ(C1^| .. | Cn^)+1` – 1 = 2 :sup:`VF+1` – 1 = AllOnes

P :sub:`k` :sup:`LOOP` = P0 & ~(C1^| … | Ck^) = P0^ = AllOnes

P :sub:`k` :sup:`EXIT` = P0 & Ck & ~(C1^| … | Ck-1^) = AllZeros

That is, vector body does not need any predication anymore and loop exit blocks just disappear. In other words, the loop is vectorized as if there is no dd-exits except one early exit at the start of the loop. One key point to note here is that this only holds because we satisfy hoistability safety and speculation safety (which we will talk below). Here is the vectorized loop with the single-exit vectorized condition:

.. code::

  i=0;
  If ( I < N) {
  for(i^; i^ < N; ++i^) {
    if(anyof(C1^) != 0) {
       break;
    }   
    I0^;
    I2^;
  }
  for(j=i^[VF]; j < N; ++j) {
    I0; 
    if(C1) {
        I1; 
        break;
    }   
    I2; 
  }
  }
  


Simple Approach Hoistability
============================

The general approach required hoisting safety for all conditions guarding dd-exits. The simplified approach doesn’t impose any new requirements. So hoistability requirement for dd-exit conditions remains the same. In the above example, if I0 is `c[i] = a[i] + b [i]` and  C1 is `if (c[i] < X)`, then we cannot *safely hoist* C1 before I0.


Simple approach Speculatability
===============================
Instead of building P0, P1, … predicates this approach requires evaluation of `anyof(C1^| .. | Cn^)` at the beginning of the loop. So, it still should be valid to safely speculate dd-exiting conditions. Fortunately, “freezing” technique still works here. Indeed, since ‘poison’ value can only appear at the exiting vector iteration, the loop can’t be exited at earlier iterations. At the same time if some dd-exit guarded by Ci is taken on iteration ‘m’ (will have ‘1’ at position ‘m’), then `anyof(freeze(C1^)| .. | freeze(Cn^))` will be evaluated to ‘1’ as well because disjunction of ‘1’ with ‘undef’ gives ‘1’ and the exit will be taken as well. 

Despite apparent similarity there is one important difference between the approaches. Namely, in the “simplified” approach, it’s always safe to exit vector loop earlier and continue with the scalar loop. That gives us an opportunity to insert extra guards that weren’t present in the original loop to prove speculation safety.
Let’s consider the example from figure 7 once again. Assume, ‘b’ is provenly dereferenceable in the range from 0 to M. Then all we need to do is to simply guard ‘b[x]’ by checking that x is in the range from 0 to M condition. If we can prove that M == K then c1 can be eliminated from the later guard. 

.. code::

  while(true) {
    int x^ = a^; 
    int x1^ = freeze(x^);
    bool c3^ = (0^ <=x1^ < M^);
    if (anyof(c3^)) break;
    char y^ = b^[x^];
    char y1^ = freeze(y);
    bool c1^ = (0^ <=x1^ < K^);
    bool c2^ = (y1^ == 0^);
    if (anyof(c1^ | c2^)) break;
    foo(x^);
    bar(y^);
    i += VF;
    if (!(0 <= i < N)) break; 
  }

Simple Approach Cost modelling
==============================

There is a pretty significant difference in cost  between the approaches. This is because each approach works better in certain scenarios:

  * The Simple approach is cheaper for the vectorized loop since each vector instruction is not predicated (we have the early vectorized exit at the start of the loop)
  * The simple approach may require the scalar loop to run several iterations since we exit the vectorized loop when the vectorized early exit fails, while in the general approach we can tail fold the scalar post loop into the vectorized loop.

The main problem with early exit vectorization cost modelling is that we do not know how many iterations are actually run, so the scalar post loop if not tail folded can be running more iterations compared to the vectorized version.

Simple Approach Live-Outs
=========================

Under C1^| … | Cn^ == 0 assumption, last value extraction mask transforms to:

EMask(X) = (Pi | … | Pj) = AllOnes

X = Extract(X^, CLSNZ(EMask(X))) = X = Extract(X^, VF))

Expectedly, live outs should be calculated the same way as during “normal” vectorization, I.e. we extract the last lane of the last vectorized iteration.



“General” vs. “Simple” approaches
----------------------------------

There are 5 focus areas that have been discussed in regard to dd-exiting loops vectorization: predication, live outs, hoistability, speculatability and cost modeling. Let’s see what it will take to support each of them for both approaches.

“General” vs. “Simple”: Predication
   One of the main differences is how predication should be handled. The “general” approach requires full predication. Fortunately, current implementation already has support for the predication so it should not be a big deal.


“General” vs. “Simple”: Hoistability
  Hoist safety analysis is the same in both cases and not a big deal since it has already been implemented in other part of the compiler.

“General” vs. “Simple”: Speculatability
  Speculation safety analysis is one of the most important things from practical point of view because many real life examples involve loads speculation. An ability to insert extra guards in the “simple” approach can be critical. We can start with speculatability of primitive arrays and those without indirect memory accesses. It boils down to proving dereferencability of the array within the maximum iterations executed within the vector loop. There are couple of ways to do this:

* if the array is statically allocated with K bytes, then we know we need the vectorized loop to stop at min(K, N).  
* If the array is dynamically allocated using an allocation function, we can rely on the allocsize attribute to form a dynamic check for the vectorized loop.
* If there is an existing check that the array is accessed up to N elements in the loop and there is a dereferenceable attribute on the start of the array, we can use this fact to ensure that we will never vectorize past the dereferenceable bytes.

“General” vs. “Simple”: Cost model
	Even though estimated cost may differ significantly for the two cases it’s not expected to require much implementation efforts. 

“General” vs. “Simple”: Live outs
   The critical difference is in live outs support. The “general” approach requires special handling of exit blocks (either through predication or explicit control flow) and tracking of last value extraction mask for each live-out individually. The “simple” approach doesn’t require any extra efforts comparing to “normal” case because live outs are naturally handled by scalar post loop.


An approach without changing existing Loop Vectorizer code
----------------------------------------------------------

There is one extra consideration not explicitly discussed so far but has potential to drive our choice of the approach to implement. As careful reader has already noted the “simple” approach has very few differences with “normal” vectorization case. That not only makes it simpler to support it in the current vectorizer but opens an opportunity to implement it as a standalone pass. The process looks the following way. First, the original loop is cloned and preprocessed to remove dd-exits and hoist corresponding conditions. Hoisting and speculation safety should be proven before doing that. Next, the resulting cloned loop is passed to the vectorizer. Finally, vectorized loop is postprocessed. During postprocessing an early exit is inserted, and live outs are fixed up to account for new exit. In addition, scalar prologue produced by the vectorizer is substituted with the original scalar loop. Cost estimation should also be corrected because hoisted dd-exit conditions are speculatively executed in the vector version and may be conditionally executed in scalar version. 
