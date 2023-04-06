# Writing and Coding Guidelines

This project targets Coq *non*-experts. Accordingly, great emphasis is placed on keeping it as simple and as accessible as possible.

## Core Principles

1. **Readability** matters most. Specifications that are difficult to grasp are fundamentally no more trustworthy than pen&paper proofs.
2. Being **explicit** is good. The overarching goal is to make it easy for the (non-expert) reader. Being explicit and (within reason) verbose and at times repetitive helps to make a spec more readable because most statements can then be understood within a local scope. Conversely, any advanced "magic" that works behind the scenes can quickly render a spec unreadable to novices.
3. **Good names** are essential. Choose long, self-explanatory names. Even if this means "more work" when typing the name a lot, it greatly helps with providing a helpful intuition to the reader. (Note to advanced users: if you find the long names annoying, consider using [Company Coq](https://github.com/cpitclaudel/company-coq)'s auto-completion features.)
4. **Comment** profusely. Make an effort to comment all high-level steps and definitions. In particular, comment all hypotheses, definitions, lemmas, etc.
5. **Keep it simple.** Shy away from advanced Coq techniques. At the very least, the spec and all lemma/theorem claims should be readable and understandable with a basic understanding of Coq (proofs are not expected to be readable).


## Readability Advice

- Use many, mostly short sections. Sections are a great way to structure code and to guide the reader; they serve the reader by establishing a local scope that is easier to remember.
- Keep definitions and proofs in separate sections, and ideally in different files. This makes the definitions short, and more clearly separates the computation of the actual analysis results from their validity arguments.
- Make extensive use of the `Hypothesis` feature. Hypotheses are very readable and are accessible even to non-Coq users, especially when paired with self-explanatory names.
- Consider renaming general concepts with `let` bindings to introduce local names that are more meaningful. 
- Interleave running commentary *as if you were writing a paper* with the actual definitions and lemmas. This helps greatly with making the spec more accessible to everyone. See [`results.fifo.rta`](../results/fifo/rta.v) for a nice example  of this style.
- When commenting, be careful not to leave any misspelled words: Prosa's CI system includes a spell-checker that will flag potential errors.
- When comments have to contain variable names or mathematical notation, use square brackets (e.g. `[job_cost j]`). You can nest square brackets _only if they are balanced_: `[[t1,t2)]` will not work. In this case, use `<<[t1,t2)>>`.
- The vocabulary of the spell-checker is extended with the words contained in [`scripts/wordlist.pws`](../scripts/wordlist.pws). Add new words only if strictly necessary.
- Document the sources of lemmas and theorems in the comments. For example, say something like "Theorem XXX in (Foo & Bar, 2007)", and document at the beginning of the file what "(Foo & Bar, 2007)" refers to.


## Naming Conventions

1. For consistency, start the name of hypotheses with `H_`.
2. For case a case analysis of `foo`, use `foo_cases` as the lemma name.
3. For a basic lemma that is intended as a rewriting rule to avoid unfolding a definition `foo` directly, use `foo_def` as the lemma name.
4. Consistently name predicates that express that something "is valid" (i.e., satisfies basic assumptions) as `valid_*` or `respects_*`.
Examples: `valid_schedule`, `taskset_respects_sporadic_task_model`.
5. Consistently name sections that define what it means to be valid w.r.t. to some concept `Foo` as `ValidFoo`.
Examples: `ValidSchedule`,  `ValidTask`, `ValidJobOfTask`, `ValidJobsOfTask`.
6. Job parameters are always prefixed with `job_`.
Examples: `job_cost`, `job_arrival`, `job_deadline`.
7. Task parameters are always prefixed with `task_`.
Examples: `task_cost`, `task_deadline`.
8. We do not follow ssreflect's concise but not so self-explanatory naming scheme.
9. Section and typeclass names should use [camel case](https://en.wikipedia.org/wiki/Camel_case) and lemma and definition names should use [snake case](https://en.wikipedia.org/wiki/Snake_case).

## Use of Spaces
1. Avoid trailing white-space characters in all files. (Use `M-x delete-trailing-whitespace` in `emacs` to delete trailing white-space characters. Add `(add-hook 'before-save-hook 'delete-trailing-whitespace)` to your `~/.emacs` file to automate this.)
2. In lemmas, hypotheses, variable and definition declarations, follow modern Coq style by using a space before and after each colon. For example:

```
Variable foo : ItsType.

Variables bar baz : TheirType.

Context {SomeConcept : ATypeClass}.

Hypothesis H_foo_at_least_3 : foo >= 3.

Lemma foo_lower_bound : foo + 1 >= 4.
```


## Coq Features

- We use type classes sparingly. Primarily, type classes are used to introduce new job and task parameters, and to express key modeling assumptions (e.g., whether jobs can self-suspend or not).
- We rely heavily on type inference. Top-level definitions do *not* require type annotations if the semantics are clear from context and Coq can figure out the specific types.
- We tend to not use a lot of custom syntax/notation. Heavy use of custom syntax reduces readability because readers are forced to remember all local syntax definitions.
- We rely heavily on ssreflect notation.

### Implicit Arguments

Implicit arguments are a convenient feature to avoid typing things
that can be guessed by the system. However, we should be careful not
to overuse them. Although perfectly crafting implicit arguments can be
a subtle art, we can first follow the simple rule that the main thing
a definition or lemma applies to should be kept explicit.

Technically, implicit arguments are often set with curly braces
``{my_implicit_arg : nat}`` instead of parentheses
``(my_explicit_arg : nat)``. When in doubt, go for explicit
arguments.

A brief explanation of implicit arguments can be found when discussing
``cons`` in Section 1.3.1 of the
[Mathcomp book](https://math-comp.github.io/mcb/book.pdf).

## Structuring Specifications

- Split specifications into succinct, logically self-contained files/modules.
- As a rule of thumb, use one file/module per concept.
- As stated above, use `Section`s liberally within each file.
- However, avoid needless sections, i.e., a section without a single variable, context declaration, or hypothesis serves no purpose and can and should be removed.

## Stating Dependencies with `Require Import` and `Require Export`

1. Prefer `Require Export full.path.to.module.that.you.want` over `From full.path.to.module.that.you Require Export want` because (as of Coq 8.10) the latter is brittle w.r.t. the "auto-magic" module finding heuristics employed by Coq (see also: Coq issues [9080](https://github.com/coq/coq/issues/9080), [9839](https://github.com/coq/coq/issues/9839), and [11124](https://github.com/coq/coq/issues/11124)).
Exception to this rule: ssreflect and other standard library imports.
2. Avoid repetitive, lengthy blocks of `Require Import` statements at the beginning of files through the judicious use of `Require Export`.
3. As an important exception to the prior rule, do not re-export modules that contain type class instance definitions. Prosa uses type class instances to express key modeling choices; such assumptions should be made explicitly.
4. Always require external libraries first, i.e., *before* stating any Prosa-internal dependencies. This way, an addition in external libraries
cannot shadow a definition in Prosa. For example, require `mathcomp` modules before any modules in the `prosa` namespace.


## Stating Lemmas and Theorems

Prosa adheres to the following style

```
Lemma my_lemma : forall foo (bar : foo) x y z, property bar x y z.
Proof.
move=> foo bar x y z.
```
which is strictly equivalent to the (more concise but less explicit)
```
Lemma my_lemma foo (bar : foo) x y z : property bar x y z.
Proof.
```

As discussed in [#86](https://gitlab.mpi-sws.org/RT-PROOFS/rt-proofs/-/issues/86), this choice of style is deliberate. Roughly speaking, the rationale is that the explicit use of  `forall` increases readability for novice users and those using Prosa primarily in "read-only mode."

While the explicit `forall` use is admittedly slightly more verbose and cumbersome for proof authors, the majority of project participants feels that the positives (self-explanatory syntax, readability) outweigh the costs (annoyance felt by more experienced users). Therefore, when stating and proving new lemmas, or when refactoring existing lemmas, please adhere to the preferred style, which is to make the `forall` explicit.


## Writing Proofs

When writing new proofs, please adhere to the following rules.

### Structure

1. Keep proofs short. Aim for just a few lines, and definitely not more than 30-40. Long arguments should be structured into many individual lemmas (in their own section) that correspond to high-level proof steps. Some exceptions may be needed, but such cases should truly remain *exceptional*.
Note: We employ an automatic proof-length checker that runs as part of continuous integration to enforce this.
2. However, making proofs as concise as possible is a *non-goal*. We are **not** playing [code golf](https://en.wikipedia.org/wiki/Code_golf). If a proof is too long, the right answer is usually **not** to maximally compress it; rather, one should identify semantically meaningful steps that can be factored out and documented as local  "helper" lemmas. Many small steps are good for readability.
3. Make use of the structured sub-proofs feature (i.e., indentation with `{` and `}`, or bulleted sub-proofs with `-`, `+`, `*`) to structure code.  Please use the bullets in the order `-`, `+`, `*` so that Proof General indents them correctly. You may keep going with `--`, `++`, and `**`.
4. Make proofs "step-able." This means preferring `.` over `;` (within reason). This makes it easier for novices to learn from existing proofs.

### Maintainability

Generally try to make proofs as robust to (minor) changes in definitions as possible. Long-term maintenance is a major concern.

1. Make use of the `by` tactical to stop the proof script early in case of any changes in assumptions.
2. General principle: **Rewrite with equalities, do not unfold definitions.**
Avoid unfolding definitions in anything but “basic facts” files. Main proofs should not unfold low-level definitions, processor models, etc. Rather, they should rely exclusively on basic facts so that we can change representations without breaking high-level proofs.
3. In particular, for case analysis, prefer basic facts that express all possible cases as a disjunction. Do not destruct the actual definitions directly.
    - Aside: Sometimes, it is more convenient to use a specific inductive type rather than a disjunction. See for instance `PeanoNat.Nat.compare_spec` in the Coq standard library or Section 4.2.1 of the [Mathcomp book](https://math-comp.github.io/mcb/book.pdf) for more details. However, we generally prefer the use of a disjunction for readability whenever possible and reasonable.
4. Do not explicitly reference proof terms in type classes (because they might change with the representation). Instead, introduce lemmas that restate the proof term in a general, abstract way that is unlikely to change and rely on those.
Guideline: do not name proof terms in type classes to prevent explicit dependencies.

### Auto-Generated Names

Some tactics, like `intros.` (without arguments) can introduce hypotheses with automatically generated names (typically `H`, `H0`, `H1`, `H2`). The use of such tactic should be avoided as they make the proofs less robust (any change can easily shift the naming). Note that ssreflect offers `move=> ?` that can be used when naming is not needed, while still being robust, because it ensures the automatically named hypotheses cannot be explicitly mentioned in the proof script. The fact that no automatically generated name is explicitly referred to is checked in the CI with the `-mangle-names` option of Coq.


### Choice of Tactics

In new code, prefer *ssreflect* style:

| Instead of… | use…  |
|:--|:--|
| `intro` or `intros` | `move` |
| `apply`| `apply:` |
| `eapply`| `apply:` |
| `apply FOO; apply BAR`| `apply/FOO/BAR` |
| `apply FOO; intro a b c` | `apply: FOO => a b c` |
| `…; simpl` | `… => /` |
| `…; try done` | `… => //` |
| `…; simpl; try done` | `… => //=` |
| `destruct` | `case:` |
| `destruct … eqn:FOO` | `case FOO: …` |
| `destruct … as [FOO｜BAR] ` | `have [FOO｜BAR] := …` |
| `edestruct FOO` | placeholder `_`, as in `(FOO _)` |
| `specialize (H_Foo x)` | `move: (H_Foo x)` |
| `induction n` | `elim: n` |

*The above list is incomplete. Please expand it as you come across missing examples.*

If you have trouble getting the ssreflect tactics to work, **ask for help** instead of reverting to non-ssreflect tactics.

**Note**: it can be effective to ask conversational AI tools such as `ChatGPT` for examples, usage instructions, and explanations. Try prompts such as: "In the context of Coq with the ssreflect library, please explain how one performs case analysis in idiomatic ssreflect style."

Document non-standard tactics that you use in the [list of tactics](doc/tactics.md). For new users, it can be quite difficult to identify the right tactics to use. This list is intended to give novices a starting to point in the search for the "right" tools.

### Forward vs backward reasoning
Although the primary focus of Prosa is on the quality of the overall structure and the specifications, good proofs are short and readable. Since Coq tends to favor backward reasoning, try to adhere to it. Forward reasoning tends to be more verbose and to generate needlessly convoluted proof trees. To get an idea, read the following snippet:

```coq
(** Let's say we have piecewise [A->B->C->D]. *)
  Variable A B C D : Prop.
  Hypothesis AB : A->B.
  Hypothesis BC : B->C.
  Hypothesis CD : C->D.

  (** And we want to prove [A->D] *)
  Lemma AD_backward :
    A -> D.
  Proof.
    move=> ?.
    apply: CD.
    apply: BC.
    by apply: AB.
  Qed.

  (** In fact, ssreflect allows us to express this even more succinctly *)
  Lemma AD_backward' :
    A -> D.
  Proof.
    move=> ?.
    by apply/CD/BC/AB.
  Qed.

  (** In contrast, the proof looks much more convoluted in forward style. *)
  Lemma AD_forward :
    A -> D.
  Proof.
    move=> ?.
    (* hmm, I have C->D. If only I had C... *)
    have I_need_C: C.
    { (* hmm, I have B->C. If only I had B... *)
      have I_need_B: B by apply: AB.
      feed BC.
      apply: I_need_B.
      by apply: BC.
    }
    feed CD.
    apply: I_need_C.
    by apply: CD.
  Qed.
```


### Misc. Hints and Tips

- Instead of writing `exists x, P x /\ Q x`, prefer `exists2 x, P x & Q x` ([see documentation](https://gitlab.mpi-sws.org/RT-PROOFS/rt-proofs/-/merge_requests/276#note_89874)). The latter saves a destruct making the intro patterns less cluttered in the proofs (i.e., one would write `=> [x Px Qx]` instead of having to write `=> [x [Px Qx]]`).

- Similarly, using the notation `[/\ A, B, C & D]` can be preferable to just `A /\ B /\ C /\ D` for the same reason. Analogous notations exist for `\/`, `&&`, and `||`. See [`Coq.ssr.ssrbool`](https://coq.inria.fr/distrib/V8.16.1/stdlib//Coq.ssr.ssrbool.html#and3) for further details.

- Avoid using lemmas from `Bool` (e.g., like `Bool.andb_orb_distrib_l`). There are more idiomatic ways of accomplishing the same things with ssreflect tactics and lemmas. To find these, look for lemmas about `andb` and `orb` in `ssr.ssrbool` with the command `Search andb orb in ssr.ssrbool`.

- Here are a couple of nice ways of doing common case analyses:
    * `have [LEQ|LT] := leqP n m.` — either `n <= m` or `n > m`.
    * `have [n_LT_m|m_LT_n|n_EQ_m] := ltngtP n m.` — either `n < m`, `m < n`, or `n = m`.
    * `have [SAME|DIFF] := boolP (same_task j j').` — are `j` and `j'` jobs of the same task?
    * `have [SAME|DIFF] := (eqVneq  (job_task j) tsk_o)` — are the task of job `j` and task `tsk_o` the same?

- It can be initially difficult to find lemmas applicable to `int` (in)equalities (e.g., when working with the GEL or ELF policies). The key is to note that `int` is just a particular instance of `ringType` or `numDomainType` and generic lemmas for these algebraic structures do apply (a lot of them are in [`ssralg`](https://math-comp.github.io/htmldoc/mathcomp.algebra.ssralg.html) or [`ssrnum`](https://math-comp.github.io/htmldoc/mathcomp.algebra.ssrnum.html)). To find applicable lemmas with `Search`, make sure to specify the appropriate notation scope `%R`. For example, `Search (_ + _)%R.` will find lemmas about addition that are applicable to `int`. As another example, `Search +%R -%R "K".` will find relevant cancellation lemmas (which by ssreflect convention include the letter "K" in their names). 

- Note that `%:R` is *not* a scope delimiter; rather, it's the injection from `nat` to a `ringType` (e.g., typically the integers in our context). For example, `Search (_%:R + _%:R)%R.` will find lemmas about the addition two injected `nat` elements in ring scope.

- If `apply: (FOO a b c)` doesn't given useful feedback, try `Check (FOO a b c)` to help with debugging the root cause.


*To be continued… Merge requests welcome: please feel free to propose new advice and better guidelines.*
