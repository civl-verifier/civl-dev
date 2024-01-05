# Split each per-layer checker procedure into pieces

See [SplittingChecks.md](SplittingChecks.md).

# Linearity

* Make linearity more general, for example:
  * Allow multiple linear annotations on a variable. See [multiple-linear-annotations.bpl](examples/multiple-linear-annotations.bpl).
  * Allow direct specification of the collector function for a variable.

# Assuming the gate of the refined action

* The justification for this feature is poorly understood. Can we drop it?
* In purity-issta.bpl, there is a loop that requires a yield at the beginning of the body to get the gate assumed.
