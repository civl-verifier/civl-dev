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

# Convert yield statements into yield invariants and modify backend so that it is aware only of yield invariants

# Add support for specifying yield invariants in a CIVL file and for including them in parallel calls

* Yield invariants, potentially invoked at different layers, should be allowed in a parallel call
* Ordinary procedures called in a parallel call should be allowed to disappear at different layers

# Async calls

* Add precondition checks at async calls at all layers
* Implement flow analysis to ensure that no global update happens between an async all and the next yield

# Split each per-layer checker procedure into pieces

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
