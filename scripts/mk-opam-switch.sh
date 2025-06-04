#!/bin/bash

set -e

# Main PROSA development dependencies
ROCQ_VERSION=9.0.0
MATHCOMP_VERSION=2.4.0
OCAML_VERSION=4.14.2

# O'Caml variant
OCAML_PKG=ocaml-variants.${OCAML_VERSION}+options
OCAML_OPTS=ocaml-option-flambda

# Default switch name
NEW_SWITCH=mathcomp-${MATHCOMP_VERSION}-rocq-${ROCQ_VERSION}-ocaml-${OCAML_VERSION}

# Create the switch
opam update
opam switch create ${NEW_SWITCH} ${OCAML_PKG} ${OCAML_OPTS}
eval $(opam env --switch=${NEW_SWITCH})

# Add the Rocq package repo
opam repo add rocq-released https://rocq-prover.org/opam/released
opam update

# Install the necessary packages
opam pin -n rocq-prover ${ROCQ_VERSION}
opam pin -n rocq-mathcomp-ssreflect ${MATHCOMP_VERSION}
opam install -y rocq-prover rocq-mathcomp-ssreflect coq-mathcomp-zify coq-coqeal
