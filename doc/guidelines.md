# Writing and Coding Guidelines

This project targets Coq *non*-experts. Accordingly, great emphasis is placed on keeping it as simple and as accessible as possible.

## Core Principles

1. **Readability** matters most. Specifications that are difficult to grasp are fundamentally no more trustworthy than pen&paper proofs.
2. Being **explicit** is good. The overarching goal is to make it easy for the (non-expert) reader. Being explicit and (within reason) verbose and at times repetitive helps to make a spec more readable because most statements can then be understood within a local scope. Conversely, any advanced "magic" that works behind the scenes can quickly render a spec unreadable to novices.
3. **Good names** are essential. Choose long, self-explanatory names. Even if this means "more work" when typing the name a lot, it greatly helps with providing a helpful intuition to the reader. (Note to advanced users: if you find the long names annoying, consider using [Company Coq](https://github.com/cpitclaudel/company-coq)'s autocompletion features.)
4. **Comment** profusely. Make an effort to comment all high-level steps and definitions. In particular, comment all hypotheses, definitions, lemmas, etc.
5. **Keep it simple.** Shy away from advanced Coq techniques. At the very least, the spec and all lemma/theorem claims should be readable and understandable with a basic understanding of Coq (proofs are not expected to be readable).


## Readability Advice

- Use many, mostly short sections. Sections are a great way to structure code and to guide the reader; they serve the reader by establishing a local scope that is easier to remember.
- Keep definitions and proofs in separate sections, and ideally in different files. This makes the definitions short, and more clearly separates the computation of the actual analysis results from their validity arguments.
- Make extensive use of the `Hypothesis` feature. Hypotheses are very readable and are accessible even to non-Coq users, especially when paired with self-explanatory names.
- Consider renaming general concepts with `let` bindings to introduce local names that are more meaningful. In many cases, this is also useful to bind necessary context to local names. For example:  
```
    Let no_deadline_is_missed :=
      task_misses_no_deadline sched tsk.
``` 
- Interleave running commentary *as if you were writing a paper* with the actual definitions and lemmas. This helps greatly with making the spec more accessible to everyone. Good example from [bertogna_fp_theory.v](../classic/analysis/global/basic/bertogna_fp_theory.v):  
```
   (** Assume any job arrival sequence... *)
    Context {arr_seq: arrival_sequence Job}.
   (** ... in which jobs arrive sporadically and have valid parameters. *)
    Hypothesis H_sporadic_tasks:
      sporadic_task_model task_period arr_seq job_task.
```
- When commenting, be careful not to leave any misspelled words: Prosa's CI system comprises a spell-checker that will signal errors.
- When comments have to contain variable names or mathematical notation, use square brackets (e.g. `[job_cost j]`). You can nest square brackets _only if they are balanced_: `[[t1,t2)]` will not work. In this case, use `<<[t1,t2)>>`.
- The vocabulary of the spell-checker is extended with the words contained in `scripts/wordlist.pws`. Add new words only if strictly necessary.
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


## Coq Features

- We use type classes sparingly. Primarily, type classes are used to introduce new job and task parameters, and to express key modeling assumptions (e.g., whether jobs can self-suspend or not).
- We rely heavily on type inference. Top-level definitions do *not* require type annotations if the semantics are clear from context and Coq can figure out the specific types.
- We tend to not use a lot of custom syntax/notation. Heavy use of custom syntax reduces readability because readers are forced to remember all local syntax definitions. 
- We rely heavily on ssreflect notation.

## Structuring Specifications

1. Split specifications into succinct, logically self-contained files/modules. As a rule of thumb, use one file/module per concept.
2. As stated above, use `Section`s liberally within each file. However, avoid needless sections, i.e., a section without a single variable, context declaration, or hypothesis serves no purpose and can/should be removed. 
3. Prefer `Require Export full.path.to.module.that.you.want` over `From full.path.to.module.that.you Require Export want` because (as of Coq 8.10) the latter is brittle w.r.t. Coq's auto-magic module finding heuristics (see also: Coq issues [9080](https://github.com/coq/coq/issues/9080), [9839](https://github.com/coq/coq/issues/9839), and [11124](https://github.com/coq/coq/issues/11124)).  
Exception to this rule: ssreflect and other standard library imports. 
4. Avoid repetitive, lengthy blocks of `Require Import` statements at the beginning of files through the judicious use of `Require Export`.
5. As an import exception to the prior rule, *never* re-export modules that contain type class instance definitions. Prosa uses type class instances to express key modeling choices; such assumptions need to be made explicit and should not be implicitly "inherited" via re-exported modules. 

## Writing Proofs

When writing new proofs, please adhere to the following rules.

### Structure

1. Keep proofs short. Aim for just a few lines, and definitely not more than 30-40. Long arguments should be structured into many individual lemmas (in their own section) that correspond to high-level proof steps. Some exceptions may be needed, but such cases should truly remain *exceptional*.  
Note: We employ an automatic proof-length checker that runs as part of continuous integration to enforce this.
2. However, making proofs as concise as possible is a *non-goal*. We are **not** playing [code golf](https://en.wikipedia.org/wiki/Code_golf). If a proof is too long, the right answer is usually **not** to maximally compress it; rather, one should identify semantically meaningful steps that can be factored out and documented as local  "helper" lemmas. Many small steps are good for readability.
3. Make use of the structured sub-proofs feature (i.e., indentation with `{` and `}`, or bulleted sub-proofs with `-`, `+`, `*`) to structure code.
4. Make proofs "step-able." This means preferring `.` over `;` (within reason). This makes it easier for novices to learn from existing proofs.


### Maintainability

Generally try to make proofs as robust to (minor) changes in definitions as possible. Longterm maintenance is a major concern.

1. Make use of the `by` tactical to stop the proof script early in case of any changes in assumptions.
2. General principle: **Rewrite with equalities, do not unfold definitions.**   
Avoid unfolding definitions in anything but “basic facts” files. Main proofs should not unfold low-level definitions, processor models, etc. Rather, they should rely exclusively on basic facts so that we can change representations without breaking high-level proofs.
3. In particular, for case analysis, prefer basic facts that express all possible cases as a disjunction. Do not destruct the actual definitions directly.
    - Aside: Sometimes, it is more convenient to use a specific inductive type rather than a disjunction. See for instance `PeanoNat.Nat.compare_spec` in the Coq standard library or Section 4.2.1 of the [Mathcomp book](https://math-comp.github.io/mcb/book.pdf) for more details. However, we generally prefer disjunctions for readability whenever possible and reasonable. 
4. Do not explicitly reference proof terms in type classes (because they might change with the representation). Instead, introduce lemmas that restate the proof term in a general, abstract way that is unlikely to change and rely on those.  
Guideline: do not name proof terms in type classes to prevent explicit dependencies.

### Tactics

- Document the tactics that you use in the [list of tactics](doc/tactics.md). For new users, it can be quite difficult to identify the right tactics to use. This list is intended to give novices a starting to point in the search for the "right" tools.


*To be continued… Merge requests welcome: please feel free to propose new advice and better guidelines.*

