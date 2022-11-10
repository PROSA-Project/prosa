# Classic Prosa (2015-2019)

---

**Deprecation warning:** Classic Prosa is no longer being maintained. Please base any new developments on "modern" Prosa. 

---

This branch preserves the *classic* version of the [Prosa open-source project](https://prosa.mpi-sws.org), as originally presented at ECRTS'16. This version of Prosa was developed from 2015 until 2019, and further maintained until 2022.

Throughout 2018–2021, Prosa was developed in the context of the [RT-Proofs research project](https://rt-proofs.inria.fr/) (funded jointly by ANR and DFG, projects ANR-17-CE25-0016 and DFG-391919384, respectively).

<center><img alt="RT-Proofs logo" src="http://prosa.mpi-sws.org/figures/rt-proofs-logo.png" width="300px"></center>


As of now, classic Prosa has been superseded by "modern Prosa" (as tracked in the main branch of this repository), which is under active development. Classic Prosa is no longer being maintained. 

This branch serves to preserve a working snapshot based on **Coq 8.16** and **mathcomp 1.15.0**. 


## Documentation

Up-to-date documentation for all branches of the main Prosa repository is available on the Prosa homepage:

- <https://prosa.mpi-sws.org/branches>

## Publications

Please see the [list of publications](https://prosa.mpi-sws.org/publications.html) on the Prosa project's homepage. 

All results published prior to 2020 build on this "classic" version of Prosa.

## Installation

First, make sure you have **Coq 8.16** and **mathcomp 1.15.0** installed.

### From Sources with `opam`

OPAM can also be used to install a local checkout. For example, this is done in the CI setup (see `.gitlab-ci.yaml`).

```bash
opam repo add coq-released https://coq.inria.fr/opam/released
opam update
opam pin add -n -y -k path coq-prosa .
opam install coq-prosa
```

### Manually From Sources

#### Dependencies

Besides on Coq itself, Prosa depends on 

1. the `ssreflect` library of the [Mathematical Components project](https://math-comp.github.io),
2. the [Micromega support for the Mathematical Components library](https://github.com/math-comp/mczify) provided by `mczify`, and

These dependencies can be easily installed with OPAM. 

```bash
opam install -y coq-mathcomp-ssreflect<=1.15.0 coq-mathcomp-zify
```

#### Compiling Prosa

Assuming all dependencies are available (either via OPAM or compiled from source, see the [Prosa setup instructions](http://prosa.mpi-sws.org/setup-instructions.html)), compiling Prosa consists of only two steps.

First, create an appropriate `Makefile`.

```bash
./create_makefile.sh
```

Second, compile the library.

```bash
make -j
```

Depending on how powerful your machine is, this will take a few minutes.

## Generating HTML Documentation

The Coqdoc documentation (as shown on the [webpage](http://prosa.mpi-sws.org/documentation.html)) can be easily generated with the provided `Makefile`:

- `make htmlpretty -j`  --- pretty documentation based on CoqdocJS (can hide/show proofs),
- `make gallinahtml -j` --- just the specification, without proofs,
- `make html -j`  --- full specification with all proofs.

