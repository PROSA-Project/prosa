# Prosa: Formally Proven Schedulability Analysis

This repository contains the main Coq specification & proof development of the [Prosa open-source project](https://prosa.mpi-sws.org), which was launched in 2016. As of 2018, Prosa is primarily being developed in the context of the [RT-Proofs research project](https://rt-proofs.inria.fr/) (kindly funded jointly by ANR and DFG, projects ANR-17-CE25-0016 and DFG-391919384, respectively).

<center><img alt="RT-Proofs logo" src="http://prosa.mpi-sws.org/figures/rt-proofs-logo.png" width="300px"></center>

## Publications

Please see the [list of publications](http://prosa.mpi-sws.org/documentation.html#publications) on the Prosa project's homepage. 

## Directory and Module Structure

The directory and module structure is currently undergoing a fundamental reorganization. 

- [classic/](classic/): This module contains the "classic" version of Prosa as first presented at ECRTS'16.  
All results published prior to 2020 build on this "classic" version of Prosa.
- [util/](util/): A collection of miscellaneous "helper" lemmas and tactics. Used throughout the rest of Prosa.
- [restructuring/](restructuring/): The new, refactored version of Prosa. Currently still under heavy development. This part of Prosa will soon move out of the `restructuring` namespace. 
- [scripts/](scripts/): Scripts and supporting resources required for continuous integration and documentation generation.

## Dependencies 

Besides Coq itself, Prosa's only external dependency is the ssreflect library of the [Mathematical Components project](https://math-comp.github.io).

Prosa always tracks the latest stable versions of Coq and ssreflect. We do not maintain compatibility with older versions of either Coq or ssreflect.

## Compiling Prosa

Assuming ssreflect is available (either via OPAM or compiled from source, see the [Prosa setup instructions](http://prosa.mpi-sws.org/setup-instructions.html)), compiling Prosa consists of only two steps.

First, create an appropriate `Makefile`.

```
./create_makefile.sh
```

Second, compile the library.

```
make -j
```

## Documentation

Up-to-date documentation for all branches of the main Prosa repository is available at <https://prosa.mpi-sws.org/branches>.


## Generating HTML Documentation

The Coqdoc documentation (as shown on the [webpage](http://prosa.mpi-sws.org/documentation.html)) can be easily generated with the provided `Makefile`:

- `make htmlpretty -j`  --- pretty documentation based on CoqdocJS (can hide/show proofs),
- `make gallinahtml -j` --- just the specification, without proofs,
- `make html -j`  --- full specification with all proofs.


Since Coqdoc requires object files (`*.vo`) as input, please make sure that the code is compilable.

## Commit and Development Rules

We very much welcome external contributions. Please don't hesitate to [get in touch](http://prosa.mpi-sws.org/get-in-touch.html)!

To make things as smooth as possible, here are a couple of rules and guidelines that we seek to abide by.

1. Always follow the project [coding and writing guidelines](doc/guidelines.md).

2. Make sure the master branch "compiles" at each commit. This is not true for the early history of the repository, and during certain stretches of heavy refactoring, but going forward we should strive to keep it working at all times. 

3. It's ok (and even recommended) to develop in a (private) dirty branch, but clean up and rebase (i.e., `git-rebase -i`) on top of the current master branch before opening a merge request.

4. Create merge requests liberally. No improvement is too small or too insignificant for a merge request. This applies to documentation fixes (e.g., typo fixes, grammar fixes, clarifications, etc.)  as well.

5. If you are unsure whether a proposed change is even acceptable or the right way to go about things, create a work-in-progress (WIP) merge request as a basis for discussion. A WIP merge request is prefixed by "WIP:". 

6. We strive to have only "fast-forward merges" without merge commits, so always rebase your branch to linearize the history before merging. (WIP branches do not need to be linear.)

7. Recommendation: Document the tactics that you use in the [list of tactics](doc/tactics.md), especially when introducing/using non-standard tactics.

8. If something seems confusing, please help with improving the documentation. :-)

9. If you don't know how to fix or improve something, or if you have an open-ended suggestion in need of discusion, please file a ticket. 
