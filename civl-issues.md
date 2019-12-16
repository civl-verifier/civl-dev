# Annotations that used to exists in CIVL

What was their purpose and are they subsumed or unnecessary now?

* pure: subsumed by instrumentation procedures?
* extern: Yielding procedure without implementation. Attached atomic action not
  subject to commutativity checks.

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
