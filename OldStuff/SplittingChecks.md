# Improving verification performance by splitting noninterference checks

## Status Quo

Currently, for every yielding procedure `P` and layer `n` it exists on,
there is a procedure `P_n` generated that simultaneously encodes the
following checks:

1. Refinement (only at the disappearing layer)
2. Sequential correctness (i.e., pre- and postconditions, loop invariants, etc.)
3. Noninterference

Noninterference is checked in `P_n` as follows.

```
procedure P_n(...)
{
  // nondeterministically goto CallToYieldProc at every yield point

  CallToYieldProc:
    call og_yield_n(...);
}

procedure og_yield_n(...)
{
  // P1 to Pm are all yielding procedures at layer n
  goto L1, ..., Lm;

  L1: call Impl_YieldChecker_P1_n(...); return;
  ...
  Lm: call Impl_YieldChecker_Pm_n(...); return;
}

procedure Impl_YieldChecker_Pi_n()
{
  // I1 to Ir are all yield invariants in Pi at layer n
  goto L1, ..., Lr;

  L1: assume I1(oldState); assert I1(newState); return;
  ...
  Lr: assume Ir(oldState); assert Ir(newState); return;
}
```
## The Problem

It seems that putting all noninterference checks into a single procedure
significantly degrades the prover performance. Concretely, in `GC.bpl`
the procedure `GarbageCollect_100` calls `og_yield_100` which checks
noninterference w.r.t 12 procedures. When commenting out all but one
noninterference check verification is very fast, but when adding more and
more checks simultaneously verification time goes up a lot or even makes
the prover fail.

## Proposed Solution

We would like to separate noninterference checks from refinement and
sequential correctness and also split them into smaller chunks as follows.

```
procedure NoninterferenceChecker_P_Pi_n(...)
{
  // nondeterministically goto CallToYieldProc at every yield point

  CallToYieldProc:
    call Impl_YieldChecker_Pi_n(...);
}
```

Thus we duplicate the code of `P` for noninterference checking w.r.t.
every other procedure `Pi`. Of course refinement checking and sequential
verification should not be performed over and over again.
