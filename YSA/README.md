Illustrations of the automata used for yield-sufficiency checking (in YieldTypeChecker.cs).

Grey color marks initial states, and double circles mark final states.

* Current implementation uses `Atomicity` and `Bracket`.
* Previously `A`, `B`, and `C` were used.

`Atomicity` is `C` with two nondeterministic edges removed, and `Bracket`
unifies `A` and `B` (fixing a bug related to calls to introduction procedures).
