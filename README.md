# RT-PROOFS

This repository contains the main Coq proof spec & proof development of the RT-PROOFS project.

## Directory Structure

The Prosa directory is organized in a hierarchy: while generic, reusable foundations stay in
the upper levels, definitions for specific analyses should go deeper into the directory tree.

### Base Directories

Currently, Prosa contains the following base directories:

- **model/:** Specification of task and scheduler models, as well as generic lemmas related to scheduling.
	  
- **analysis/:** Definition, proofs and implementation of schedulability analyses.

- **implementation/:** Instantiation of each schedulability analysis with concrete task and scheduler implementations.
		       Testing the main theorems in an assumption free environment shows the absence of contradictions.

### Internal Directories

The major concepts in Prosa are specified in the *model/* folder.

- **model/arrival:** Arrival sequences and arrival bounds
- **model/schedule:** Definitions and properties of schedules

Inside *model/schedule*, you can find the different classes of schedulers.

- **model/schedule/uni:** Uniprocessor scheduling.
- **model/schedule/global:** Global scheduling.
- **model/schedule/partitioned:** Partitioned scheduling.
- **model/schedule/apa:** APA scheduling.

### Extending Prosa

When adding a new model or analysis to Prosa, please extend the corresponding directory.
For example, the schedulability analysis for global scheduling with release jitter is organized as follows.

- **model/schedule/global/jitter:** Definitions and lemmas for global scheduling with release jitter.
- **analysis/global/jitter:** Analysis for global scheduling with release jitter.
- **implementation/global/jitter:** Implementation of the concrete scheduler with release jitter. 

## Generating HTML Documentation

The Coqdoc documentation (as shown on the [webpage](http://prosa.mpi-sws.org/documentation.html)) can be easily generated with `Make`:

```$ make html -j 4``` *Documentation with proofs*

```$ make gallinahtml -j 4``` *Documentation without proofs*

```$ make htmlpretty -j 4``` *Pretty documentation (can also hide/show proofs)*

Since Coqdoc requires object files as input, please make sure that the code is compilable.

## Commit and Development Rules

1. Always follow the project [coding and writing guidelines](doc/guidelines.md).

2. Make sure the master branch "compiles" at each commit. This is not true for the early history of the repository, but going forward we should strive to keep it working at all times. 

3. It's ok to develop in a (private) dirty branch, but then clean up and `git-rebase -i` on top of the current master before merging your work into master.

4. It's usually a good idea to ask first on the mailing list before merging a substantial change.

5. Pushing fixes, small improvements, etc. is always ok. 

6. Document the tactics that you use in the [list of tactics](doc/tactics.md).

7. Whenever you have time available, please help with extending the documentation. :-)