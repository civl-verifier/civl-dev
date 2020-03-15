# Linearity

* Make linearity more general, for example:
  * Allow multiple linear annotations on a variable.
  * Allow the directly specification of the collector function for a variable.
* Implement linearity checking of atomic actions w.r.t. pending asyncs.

# Yield Checking

* Implement a more well-understood version of yield-sufficiency checking. In
  particular w.r.t. async calls.

# Split VCs into smaller ones

See [SplittingChecks.md](SplittingChecks.md).

# Cooperation checking

The soundness of yield sufficiency checking depends on cooperation which is not
checked currently.

# Parallel calls

The type checking of parallel calls and desugaring does not match the
description in `Layered concurrent programs` and the upcoming CAV submission.

# Inductive sequentialization

* Noninterferenche checking w.r.t. pending asyncs
* Precondition checking of async call at disappearing layer of caller
* Cooperation checking

# Yield invariants

Shall we add yield invariants and drop yield statements from CIVL?

# Global invariants

A global invariant has similar syntax to yield invariants but is not allowed any
input parameters and cannot refer to old snapshot of global variables. A global
invariant must be preserved by each atomic action (as opposed to yield-free code
fragments) and must be satisfied by the initial state of the program. It can be
injected as an assume at any control location in a procedure implementation, the
typical candidates being a loop head or immediately after a procedure call.
