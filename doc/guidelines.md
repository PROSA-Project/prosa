# Writing and Coding Guidelines

This project targets Coq *non*-experts. Accordingly, great emphasis is placed on keeping it as simple and as accessible as possible.

## Core Principles

1. **Readability** matters most. Specifications that are difficult to grasp are fundamentally no more trustworthy than pen&paper proofs.

2. Being **explicit** is good. The overarching goal is to make it easy for the (non-expert) reader. Being explicit and (within reason) verbose and at times repetitive helps to make a spec more readable because most statements can then be understood within a local scope. Conversely, any advanced "magic" that works behind the scenes can quickly render a spec unreadable to novices.

3. **Good names** are essential. Choose long, self-explanatory names. Even if this means "more work" when typing the name a lot, it greatly helps with providing a helpful intuition to the reader. (Note to advanced users: if you find the long names annoying, consider using [Company Coq](https://github.com/cpitclaudel/company-coq)'s autocompletion features.)
   
4. **Comment** profusely. Make an effort to comment all high-level steps and definitions. In particular, comment all hypotheses, definitions, lemmas, etc.
   
5. **Keep it simple.** Shy away from advanced Coq techniques. At the very least, the spec and all lemma/theorem claims should be readable and understandable with a basic understanding of Coq (proofs are not expected to be readable).


## Specific Advice

- Use many, mostly short sections. Sections are a great way to structure code and to guide the reader; they serve the reader by establishing a local scope that is easier to remember.

- Keep definitions and proofs in separate sections, and ideally in different files. This makes the definitions short, and more clearly separates the computation of the actual analysis results from their validity arguments.

- Make extensive use of the `Hypothesis` feature. Hypotheses are very readable and are accessible even to non-Coq users, especially when paired with self-explanatory names.

- For consistency, start the name of hypotheses with `H_`.

- Make proofs "step-able." This means preferring `.` over `;` (within reason). This makes it easier for novices to learn from existing proofs.

- Making proofs as concise as possible is a *non-goal*. We are **not** playing [code golf](https://en.wikipedia.org/wiki/Code_golf).

- Document the tactics that you use in the [list of tactics](doc/tactics.md). For new users, it can be quite difficult to identify the right tactics to use. This list ist intended to give novices a starting to point in the search for the "right" tools.

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

- Document the sources of lemmas and theorems in the comments. For example, say something like "Theorem XXX in (Foo & Bar, 2007)", and document at the beginning of the file what "(Foo & Bar, 2007)" refers to.


## Writing Proofs

- Keep proofs short. Aim for just a few lines, and definitely not more than 30-40. Long arguments should be structured into many individual lemmas (in their own section) that correspond to high-level proof steps. Some exceptions may be needed, but such cases should truly remain *exceptional*.  
Note: We employ an automatic proof-length checker that runs as part of continuous integration to enforce this.

- Make use of the structured sub-proofs feature (i.e., indentation with `{` and `}`, or bulleted sub-proofs with `-`, `+`, `*`) to structure code.

- Generally try to make proofs as robust to (minor) changes in definitions as possible. Longterm maintenance is a major concern.

- Make use of the `by` syntax to stop the proof script early in case of any changes in assumptions.

- General principle: Rewrite with equalities, do not rely on definitions.

- Avoid unfolding definitions in anything but “basic facts” files. Main proofs should not unfold low-level definitions, processor models, etc. Rather, they should rely exclusively on basic facts so that we can change representations without breaking high-level proofs.

- In particular, for case analysis, prefer basic facts that express all possible cases as a disjunction. Do not destruct the actual definitions directly.


- Naming suggestion: for case a case analysis of foo, use foo_cases as the lemma name.


- Do not explicitly reference proof terms in type classes (because they might change with the representation). Instead, introduce lemmas that restate the proof term in a general, abstract way that is unlikely to change and rely on those. Guideline: do not name proof terms in type classes to prevent explicit dependencies.


*To be continued… please feel free to propose new advice and better guidelines.*

