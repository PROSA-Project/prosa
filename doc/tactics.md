# List of Tactics

In effort to make it easier for new users to get started with the Prosa project, the idea is to maintain a list of the tactics used in the project in this file.

Each tactic should be named and briefly described (just a few sentences). Please add links to additional documentation elsewhere (if available).

## Tactics from VBase

Tactics taken from the standard library of Viktor Vafeiadis.

- `ins`: combination of `intros`, `simpl` and `eauto`. Some trivial proofs follow from `by ins`.

- `des`: breaks all conjunctions in the local context, applies any simple substitutions via `subst`, and breaks any disjunctions in the local context into separate cases that are to be proved individually as subgoals.

- `desc`: same as `des`, but does not break disjunctions.

- `desf`: Combination of `des` with the evaluation of 'if-then-else' conditions. It performs a case analysis of every 'if-then-else' in the local context
   or in the goal. If it becomes slow in large proofs, you can remove unnecessary assumptions (e.g., with `clear - ...`) before applying the tactic.

- `desf_asm`: same as `desf`, but only applied to the assumptions in the local context.

- `exploit H`: When applied to a hypothesis/lemma H, converts pre-conditions into goals in order to infer the post-condition of H, which is then added to the local context.

- `feed H`: Same as exploit, but only generates a goal for the first pre-condition. That is, applying exploit to (H: P1 -> P2 -> P3) produces (H: P2 -> P3) and converts P1 into a goal. This is useful for cleaning up induction hypotheses.

- `feed_n k H`: Same as feed, but generates goals up to the k-th pre-condition.

- `specialize (H x1 x2 x3)`: instantiates hypothesis H in place with values x1, x2, x3.

*To be continued… please help out.*

## Tactics from `ssreflect`

- `have y := f x1 x2 x3`: Creates an alias to (f x1 x2 x3) called y (in the local context). Note that f can be a function or a proposition/lemma.

*To be written… please feel free to start.*


## Standard Coq Tactics

*To be written… please feel free to start.*

