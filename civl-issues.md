# Layer ranges for local variables

* Enable a local variable, including parameters, to be labeled by a layer range.
* Enhance type checking so that if x flows into y, then layer range of y is contained in that of x.

# Allow an introduction procedure to be called at layers other than disappearing layer of enclosing procedure

* All outputs of a call annotated by layer x must be received in variables with layer range [x,x].
* Outputs of an introduction call can only flow into other introduction calls and assertions.

# Implement hiding of parameters in refinement checking

* Infer hidden parameters by examining layer ranges of parameters of procedure
* Incorporate hiding in the refinement checking based on the CAV submission

# Implement calls to procedures in refinement checking

# Eliminate special treatment of skip procedures

* Compile skip procedures as atomic action procedures that refine the skip action

# Convert yield statements into yield invariants and modify backend so that it is unaware of yield statements

# Parallel calls

The type checking of parallel calls and desugaring is restricted compared to the
description in `Layered concurrent programs` and the CAV submission.

# Add support for specifying yield invariants in a CIVL file and for including them in parallel calls

# Async calls

* Drop snapshotting at async calls
* Implement sound precondition checking for async calls (either by flow analysis or by collecting async calls)

# Split VCs into smaller ones

See [SplittingChecks.md](SplittingChecks.md).

# Pending asyncs

* Noninterference checking w.r.t. pending asyncs
* Implement linearity checking of atomic actions w.r.t. pending asyncs.

# Cooperation checking

The soundness of yield sufficiency checking and inductive sequentialization
depends on cooperation which is not checked currently.

# Linearity

* Make linearity more general, for example:
  * Allow multiple linear annotations on a variable.
  * Allow direct specification of the collector function for a variable.
