This is a work-in-progress directory and part of the larger Prosa restructuring effort. As parts in Prosa are changed to comply with the “new style”, they are placed here.

The behavior directory collects all definitions and basic properties of system behavior (i.e., trace-based semantics). Changes here are sensitive since this is the part of the library that everyone is going to use, so changes here should be discussed early.

The model directory collects all definitions and basic properties of system models (e.g., sporadic tasks, arrival curves, scheduling policies etc.). One should port and validate a new system model before the corresponding analysis.

The analysis directory collects all definitions of system properties (e.g., schedulability, response time etc.), analysis results and proofs. The stucture of this directory is not clear yet.

# Remarks

We have chosen and applied some renaming rules for sections and definitions, cf. arrival_sequence.v and sporadic.v. Basically, we try to consistenly use `Valid*` , `*Properties` for section names about a concept `*` and `respects_*`, `valid_*` for definitions about a system model `*`.
