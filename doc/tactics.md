# List of Tactics

In effort to make it easier for new users to get started with the Prosa project, the idea is to maintain a list of the tactics used in the project in this file.

Each tactic should be named and briefly described (just a few sentences). Please add links to additional documentation elsewhere (if available).

## Tactics from VBase

Tactics taken from the standard library of Viktor Vafeiadis.

- `ins`: combination of `intros`, `simpl` and `eauto`. Some trivial proofs follow from `by ins`.

- `exploit H`: When applied to a hypothesis/lemma `H`, converts pre-conditions into goals in order to infer the post-condition of `H`, which is then added to the local context.

- `feed H`: Same as exploit, but only generates a goal for the first pre-condition. That is, applying exploit to `H: P1 -> P2 -> P3` produces `H: P2 -> P3` and converts `P1` into a goal. This is useful for cleaning up induction hypotheses.

- `feed_n k H`: Same as feed, but generates goals up to the `k`-th pre-condition.

- `specialize (H x1 x2 x3)`: instantiates hypothesis `H` in place with values `x1`, `x2`, and `x3`.

*To be continued… please help out.*

## Tactics from `ssreflect`

- `have y := f x1 x2 x3`: creates an alias to `f x1 x2 x3` called `y` (in the local context). Note that `f` can be a function or a proposition/lemma. It's usually easier to read than `move: (f x1 x2 x3) => y`.

*To be continued… please help out.*

## Standard Coq Tactics

Generally speaking, in new code, prefer `ssreflect` tactics over standard Coq tactics whenever possible. While the current code base is a mix of classic Coq tactics and `ssreflect` tactics, that's only a historical accident not worth emulating. 

- `lia`: Solves arithmetic goals, including ones with `ssreflect`'s definitions (thanks to the `coq-mathcomp-zify` dependency).

*To be continued… please help out.*

## PROSA Tactics

- `move_neq_down H`: moves inequality `H : t1 <= t2` (or `H : t1 < t2`) from the context into goals as `t1 > t2` (or `t1 >= t2`)
- `move_neq_up H`: the reverse operation that moves inequality `t1 <= t2` (or `t1 < t2`) from goals into the context as `H : t1 > t2` (or `H : t1 >= t2`)
- `interval_to_duration t1 t2 k`: any interval `[t1, t2]` can be represented as `[t1, t1 + k]` for some natural number `k`. This tactic searches for inequality `t1 <= t2` (or `t1 < t2`) in the context and replaces `t2` with `t1 + k`. Note: `k` is the name of a newly created natural number. 
- `rt_auto`: equivalent to `auto with basic_rt_facts`
- `rt_eauto`: equivalent to `eauto with basic_rt_facts`



