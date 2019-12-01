Daniel Ricketts's "async set copy" example exposed a kind of loop the cannot be
elegantly summarized with the current tactics of CIVL. Here is a potential new
tactic to summarize loops, which is somewhat related to the ideas in inductive
sequentialization.

Suppose we have the loop code `Y`, where `Y` is a block of code that can already
be proved atomic. `Y` uses a primitive break statement. The meaning of loop `Y`
is that `Y` executes repeatedly until break is hit.

Let `Y_i` be the code block obtained from `Y` by blocking exit edges (indicated
by break). Similarly, `Y_f` is the code block obtained from `Y` by blocking back
edges.

**Rule 1:**
To summarize loop `Y` with action `A`, supply action `R` such that
- `SKIP` refines `R`;
- `R` is a right mover;
- `R ∘ Y_i` refines `R`;
- `R ∘ Y_f` refines `A`.

**Rule 2:**
To summarize loop `Y` with action `L`, show that
- `Y_f` refines `L`;
- `L` is a left mover;
- `Y_i ∘ L` refines `L`;
- `Y` has a terminating execution from every state satisfying the gate of `L`.
