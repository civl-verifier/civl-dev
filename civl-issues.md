High priority:

# Layer ranges for local variables

* Enable a local variable, including parameters, to be labeled by a layer range.
* Enhance type checking so that if x flows into y, then layer range of y is contained in that of x.

# Allow an introduction procedure to be called at layers other than disappearing layer of enclosing procedure

* All outputs of a call annotated by layer x must be received in variables with layer range [x,x].
* Outputs of an introduction call can only flow into other introduction calls and assertions.

# Implement hiding of parameters in refinement checking

# Implement calls to procedures in refinement checking

# Eliminate special treatment of skip procedures

# Convert yield statements into yield invariants and modify backend so that it is unaware of yield statements

# Add support for specifying yield invariants in a CIVL file


# Async calls

We would like to treat an async call as a left mover in yield-sufficiency checking.
Therefore, we cannot depend on a yield at an async call to check the precondition
of the callee.
* Implement precondition checking for async calls
* Update yield sufficiency checking

# Pending asyncs

* Noninterference checking w.r.t. pending asyncs
* Implement linearity checking of atomic actions w.r.t. pending asyncs.

# Split VCs into smaller ones

See [SplittingChecks.md](SplittingChecks.md).

Low priority:

# Cooperation checking

The soundness of yield sufficiency checking and inductive sequentialization
depends on cooperation which is not checked currently.

# Linearity

* Make linearity more general, for example:
  * Allow multiple linear annotations on a variable.
  * Allow direct specification of the collector function for a variable.

# Parallel calls

The type checking of parallel calls and desugaring is restricted compared to the
description in `Layered concurrent programs` and the CAV submission.

