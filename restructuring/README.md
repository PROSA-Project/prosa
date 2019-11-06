# Restructed Prosa

This is a work-in-progress directory and part of the larger Prosa restructuring effort. As parts in Prosa are changed to comply with the “new style”, they are placed here. 

The following discussion is going to move to the top-level README file when the `restructuring` prefix is dropped.

## Structure 

There are four main parts of Prosa. 

The `behavior` namespace collects basic definitions and properties of system behavior (i.e., it defines Prosa's **trace-based semantics**). There are *no* proofs here. This module is mandatory: *all* results in Prosa rely on the basic trace-based semantics defined in this module. 

The `model` namespace collects all definitions and basic properties of various **system models** (e.g., sporadic tasks, arrival curves, various scheduling policies, etc.). There are only few proofs here. This module may contain multiple, mutually exclusive alternatives (e.g., periodic vs. sporadic tasks, uni- vs. multiprocessor models, constrained vs. arbitrary deadlines, etc.) and higher-level results can pick-and-choose whatever definitions are appropriate.

The `analysis` namespace collects all definitions and proofs of **system properties** (e.g., schedulability, response time, etc.). This includes a substantial library of *basic facts* that follow directly from the trace-based semantics or specific modelling assumptions. Most importantly, all high-level analysis results and virtually all proofs are located here. 

In future work, there will also (again) be an `implementation` namespace in which important high-level results are instantiated (i.e., applied) in an assumption-free environment for concrete job and task types to establish the absence of any contradiction in assumptions.
