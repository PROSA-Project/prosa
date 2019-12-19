# Prosa Analysis Library

This module provides virtually all **analysis concepts and definitions** and encapsulates the bulk of the **intermediate proofs** in Prosa. 

More precisely, this module collects all definitions that are not needed to define the behavioral semantics (found in [prosa.behavior](../behavior)) and that also do not conceptually form part of the task and system model (found in [prosa.model](../model)). For example, precise notions of "schedulability," "busy window," or "response time" are clearly analysis concepts and consequently defined here. 

The proofs found in this module are "intermediate proofs" in the sense that they are not an end in of themselves; rather, they are a means to enable the proofs of the high-level results provided in the [prosa.results](../results) module.

## Structure

The Prosa analysis library is currently organized as follows:

- [abstract](./abstract): This provides **abstract RTA** analysis framework, a general and extensible approach to response-time analysis (RTA).
- [definitions](./definitions): This folder currently collects all major and minor **analysis definitions** (such as schedulability, priority inversion, etc.).
- [transform](./transform): This folder contains procedures for transforming schedules, to be used in proofs that rely on modifying a given reference schedule in some way (e.g., the EDF "swapping argument").
- [facts](./facts): Currently the home of virtually all **intermediate proofs**. In particular, [facts.behavior](./facts/behavior) provides a library of basic facts that follow (mostly) directly from Prosa's trace semantics (as given in [prosa.behavior](../behavior)).

**NB**: It is expected that the analysis module will be further (re)organized and (re)structured in future versions of Prosa.

## Guidelines

- As a general rule, keep definitions and proofs separate, so that casual readers may read and understand the Prosa specification without encountering intermediate lemmas and proofs. 
- Prefer subfolders with many short files over fewer, longer files. 
- In each file that is specific to some system model, explicitly `Require` the specific modules that jointly constitute the assumed system model (e.g., `Require prosa.model.processor.ideal` to express that the results in a file depend on the ideal-uniprocessor assumption).