# Improving Atomic Actions

Let me recapitulate the current state of my thinking about atomic actions.
First, the goal is to satisfy both properties below simultaneously:

- It should be possible to write atomic actions imperatively using assignments
  and auxiliary variables.
- Refinement checks, commutativity checks, and nonblocking checks must not
  depend on any CIVL-introduced quantified variables.

The basic premise is that we should think of auxiliary variables as being of two
kinds, history and prophecy. Each history variable must be a (deterministic)
function of the pre-state; updates to history variables must be done via forward
assignments. Each prophecy variable must be a (deterministic) function of the
post-state; updates to prophecy variables must be done via backward assignments.
Updates to global variables can be done via either forward or backward
assignments. Each path in the atomic action must satisfy three properties:
(1) all forward assignments occur before all backward assignments,
(2) each history variable is forward-assigned before being used, and
(3) each prophecy variable is backward-assigned before being used.
This setup is sufficient to ensure that all history and prophecy variables can
be eliminated during the construction of the transition relation. It is also
flexible enough to express an arbitrary transition relation.

By following the recipe in the last paragraph, we can ensure that no quantified
variables are introduced in the construction of transition relation of
individual atomic actions. This covers our desire for refinement checking. But
quantified variables may still be introduced in the construction of composition
of two atomic actions (for commutativity checks) and the domain of an atomic
action (for nonblocking checks). I will propose recipes for these two problems
based on your idea of witnesses. The main difference between my proposal and
yours is that witnesses will be used to eliminate variables entirely rather than
serving as raw material for triggers.

In my proposal, a witness is an auxiliary variable, either history or prophecy.
Let us first consider the problem of nonblocking checks. To check that an atomic
action A is non-blocking, I have to construct a quantifier-free expression for
the domain of A. Therefore, global variables in the post-state must be
eliminated in addition to history and prophecy variables in the code of A. A
variable g can be eliminated in the post-state easily if its result can be
computed as a function of the pre-state using backward substitution (similar to
what we do for history variables). But, if g is difficult to eliminate in the
post-state, the programmer can provide a history variable h to act as a witness
for g. The witness h, similar to any history variable, represents a function on
the pre-state and we can eliminate g by using this function.

Dealing with commutativity checks is similar but more challenging. To check that
B ∘ A refines A ∘ B, we need to construct a quantifier-free expression for
A ∘ B. In addition to history and prophecy variables in A and B, we have to
eliminate the variables in the global state after executing A but before
executing B. If a variable g is difficult to eliminate in this middle state, its
witness, in general, might depend on both the pre-state and the post-state of A
o B. Thus, a witness in the code of A (or in the code of B) might not suffice by
itself. The general solution is to provide one or more history variables in A,
one or more prophecy variables in B, and separately provide a function that
looks at the values of these history and prophecy variables to create the
witness for g in the middle state.

Overall, two mechanisms need to be invented for witnesses.
- Annotation on a local variable in atomic actions to indicate that it must be
  used as a witness.
- Annotation on a function definition to indicate that the function must be used
  to create a witness for the middle state of the composition of two atomic
  actions.

--------------------------------------------------------------------------------

The function TranslateCmds below takes a sequence of commands and translates it
into another sequence of commands on which the existing computation of
transition relation can be applied. I use the notation `lambda p. p -> e` to
indicate a substitution map for prophecy variables in scope.

```
TranslateCmds([]) = []
TranslateCmds(c; C) = TranslateCmd(CalculateSubstitutionCmds(lambda p. p -> p, C), c); TranslateCmds(C)
TranslateCmd(subst, c) =
  match c {
    Assume(e) => Assume(subst(e)),
    Assign(x, e) => Assign(x, subst(e)),
    ReverseAssign(x, e) => Skip // Skip is a pseudonym for Assume(true)
  }
   
CalculateSubstitutionCmds(subst, []) = subst
CalculateSubstitutionCmds(subst, c; C) = CalculateSubstitutionCmds(CalculateSubstitutionCmd(subst, c), C)
CalculateSubstitutionCmd(subst, c) =
  match c {
    Assume(_) => subst,
    Assign(x, e) => subst,
    ReverseAssign(x, e) => lambda p. p -> subst[p][x/e]
  }
```
