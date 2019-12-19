# Prosa Model Library

This module provides Prosa's library of **system model definitions** and **common modelling assumptions**. In particular, this module defines common task models such as the sporadic task model, concepts such as self-suspensions and release jitter, and uni- and multiprocessor schedules, among many other common model elements.  

All concepts and definitions here are provided on an **opt-in basis**: for many concepts, there is no "one size fits all" definition. Rather, in the literature, there are many different reasonable alternatives to choose from, and higher-level results are free to choose whichever definition is most appropriate in their context.

For example, a higher-level result can choose to assume either the classic Liu&Layland readiness model (any pending job is ready to be executed), a release-jitter model (a job may not be ready for execution for some bounded duration after its arrival, but once it's released it can always be executed), or a dynamic self-suspension model (a job may not be ready at various points during its execution). Similarly, there are many different preemption models (fully preemptive, fully nonpreemptive, segmented limited-preemptive, floating nonpreemptive, etc.) that are all of practical relevance in different contexts.


## Structure Convention

If there is a central concept (e.g., notion of readiness, processor model, arrival model, etc.) for which there are multiple reasonable competing definitions (e.g., different readiness models such as release jitter or self-suspensions, different uni- or multiprocessor models, or different arrival models such as periodic vs. sporadic tasks vs. arbitrary arrival curves), then

1. create a folder/module corresponding to the high-level concept (e.g., `readiness`, `processor`, `task/arrival`, etc.) and

2. provide different, mutually exclusive modelling assumptions as individual files or sub-modules (e.g., `readiness.basic` vs. `readiness.jitter`, `processor.ideal` vs. `processor.varspeed`, `arrival.sporadic` vs. `arrival.arrival_curves`, etc.).

This allows other proofs to "pick and choose" just the right system model by combining once definition from each category. 

Crucially, when used in other files, modules that define new `Instance`s should be `Import`ed (not `Export`ed) to avoid inadvertently polluting the namespace with specific instantiations of generic concepts. 

This allows higher-level results to clearly state assumptions in an elegant way. For instance, it is intuitively understandable what `Require prosa.model.processor.ideal` means.

## Job and Task Parameters

Please follow the below rules when introducing new job or task parameters.

- Define new job and task parameters wherever they are first needed.  
Example: `JobJitter` is introduced in `model.readiness.jitter`, not in `behavior.job`.

- Each job/task parameter is introduced as a separate type class. For example, there are separate type classes for `JobArrival`, `JobCost`, and `JobDeadline` so that parameters can be selected and mixed as needed (e.g.,  not every type of job has necessarily a deadline). 

- For certain general concepts it can be very useful (or even essential) to state invariants that any reasonable choice must satisfy. This can be expressed as proof terms within a type class expressing the general concept. For instance, this is used in the `ProcessorState` and `JobReady` type classes, to specify their fundamental semantics. Introducing such proof terms is ok if it is truly required, or if it yields great benefits in readability elsewhere, but generally speaking **use proof terms sparingly and document their use profusely**. 

- When in doubt, avoid proof terms and instead opt for the regular Prosa way of defining a `valid_...` predicate to concisely express all properties that any reasonable interpretation of a given general concept must satisfy.