# CIVL Development

## Boogie

CIVL is implemented as part of the
[Boogie](https://github.com/boogie-org/boogie) verifier.

A "desugared" CIVL file is generated using the flag
`/CivlDesugaredFile:<file.bpl>`.

The refinement-triggers branch has the two flags `/noWitnessInference` and
`/noCommutativityTriggers` which disable parts of the code that we want to get
rid of.
