# Prosa Behavior Specification 

This module defines the **Prosa trace-based semantics**. The following rules/guidelines apply to this module:

- Files in this module must be largely self-contained and may depend only on "helper" definitions in `rt.util`. In particular, nothing in here may depend on concepts in the `model` or `analysis` modules.

- This module is purely a specification of semantics. There are no proofs.

- This behavior specification strives to be (almost) minimal. If a concept doesn't have to be defined here, if it is not required to state the basic trace semantics, then it should be introduced elsewhere. 

- The behavior specification is the universally agreed-upon foundation of Prosa. Everyone uses this; there are no alternatives to the basic definitions introduced here.

- If there are multiple competing sets of assumptions in the literature, then that's a sure sign that it should go into the `model` or `analysis` modules.

- Changes here are extremely sensitive precisely because this is the part of the library that *everyone* is going to use, so significant changes here should be discussed early and extensively.
