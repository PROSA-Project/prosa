# Prosa: Formally Proven Schedulability Analysis

This repository contains the main Coq specification & proof development of the [Prosa open-source project](https://prosa.mpi-sws.org), which was launched in 2016. As of 2018, Prosa is primarily being developed in the context of the [RT-Proofs research project](https://rt-proofs.inria.fr/) (kindly funded jointly by ANR and DFG, projects ANR-17-CE25-0016 and DFG-391919384, respectively).

<center><img alt="RT-Proofs logo" src="http://prosa.mpi-sws.org/figures/rt-proofs-logo.png" width="300px"></center>

## Documentation

Up-to-date documentation for all branches of the main Prosa repository is available on the Prosa homepage:

- <https://prosa.mpi-sws.org/branches>

## Publications

Please see the [list of publications](http://prosa.mpi-sws.org/documentation.html#publications) on the Prosa project's homepage. 

## Directory and Module Structure

The directory and module structure is organized as follows. First, the main parts, of which there are currently four.

- [behavior/](behavior/): The `behavior` namespace collects basic definitions and properties of system behavior (i.e., it defines Prosa's **trace-based semantics**). There are *no* proofs here. This module is mandatory: *all* results in Prosa rely on the basic trace-based semantics defined in this module. 
- [model/](model/): The `model` namespace collects all definitions and basic properties of various **system models** (e.g., sporadic tasks, arrival curves, various scheduling policies, etc.). There are only few proofs here. This module contains multiple, mutually exclusive alternatives (e.g., periodic vs. sporadic tasks, uni- vs. multiprocessor models, constrained vs. arbitrary deadlines, etc.), and higher-level results are expected "pick and choose" whatever definitions and assumptions are appropriate.
- [analysis/](analysis/): The `analysis` namespace collects all definitions and proof libraries needed to establish **system properties** (e.g., schedulability, response time, etc.). This includes a substantial library of *basic facts* that follow directly from the trace-based semantics or specific modelling assumptions. Virtually all intermediate steps and low-level proofs will be found here.
- [results/](results/): The `results` namespace contains all **high-level analysis results**. 


In future work, there will also (again) be an `implementation` or `examples` namespace in which important high-level results are instantiated (i.e., applied) in an assumption-free environment for concrete job and task types to establish the absence of any contradiction in assumptions.

Furthermore, there are a couple of additional folders and namespaces.

- [classic/](classic/): This module contains the "classic" version of Prosa as first presented at ECRTS'16.  
All results published prior to 2020 build on this "classic" version of Prosa.
- [util/](util/): A collection of miscellaneous "helper" lemmas and tactics. Used throughout the rest of Prosa.
- [scripts/](scripts/): Scripts and supporting resources required for continuous integration and documentation generation.

## Installation

### With OPAM

Prosa can be installed using the [OPAM package manager](https://opam.ocaml.org/) (>= 2.0)

```
opam repo add coq-released https://coq.inria.fr/opam/released
# or for the dev version (git master): https://coq.inria.fr/opam/extra-dev
opam update
opam install coq-prosa
```

### From Sources With `esy`

Prosa can be installed using [esy](https://esy.sh/).

#### Installing `esy`

`esy` itself can typically be installed through `npm`.
It should look something like this on most `apt`-based systems:
```
sudo apt install npm
sudo npm install --global esy@latest
```

#### Installing Prosa

With `esy` in place, it is easy to compile Prosa in one go. To download and compile all of Prosa's dependencies (including Coq), and then to compile Prosa itself, simply issue the command:
```
esy
```

Note that `esy` uses an internal compilation environment, which is not exported to the current shell.
To work within this environment, prefix any command with `esy`: for instance `esy coqide` to run your system’s coqIDE within the right environment.
Alternatively, `esy shell` opens a shell within its environment.

### Manually From Sources

#### Dependencies

Besides Coq itself, Prosa's only external dependency is the ssreflect library of the [Mathematical Components project](https://math-comp.github.io).

Prosa always tracks the latest stable versions of Coq and ssreflect. We do not maintain compatibility with older versions of either Coq or ssreflect.

#### Compiling Prosa

Assuming ssreflect is available (either via OPAM or compiled from source, see the [Prosa setup instructions](http://prosa.mpi-sws.org/setup-instructions.html)), compiling Prosa consists of only two steps.

First, create an appropriate `Makefile`.

```
./create_makefile.sh
```

Alternatively, to avoid compiling the older "classic" Prosa, specify the `--without-classic` option. This can speed up compilation considerably and is a good idea during development.  (It's also possible to *only* compile the "classic" Prosa by specifying the `--only-classic` option, but this is rarely needed.)

```
./create_makefile.sh --without-classic
```

Second, compile the library.

```
make -j
```

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
