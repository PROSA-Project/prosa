#!/bin/bash 

# options passed to `find` for locating relevant source files
FIND_OPTS=( . -name '*.v' ! -name '*#*' ! -path './.git/*' ! -path './with-proof-state/*' )

CoqProjectR="-R . prosa"
CoqProjectContent="-arg \"-w -notation-overriden,-parsing,-projection-no-head-constant\""

while ! [ -z "$1" ]
do
    case "$1" in
        --without-refinements)
            FIND_OPTS+=( ! -path './implementation/refinements/*' )
            ;;
        --only-refinements)
            FIND_OPTS+=( -path './implementation/refinements/*' )
            CoqProjectR="-R implementation/refinements prosa.implementation.refinements"
            ;;
        *)
            echo "Unrecognized option: $1"
            exit 1
            ;;
    esac
    shift
done

rm -f _CoqProject
echo "# Automatically created by create_makefile.sh, do not edit" > _CoqProject
echo "${CoqProjectR}" >> _CoqProject
echo "${CoqProjectContent}" >> _CoqProject

FIND_OPTS+=( -print )

# Compile all relevant *.v files
coq_makefile -f _CoqProject $(find "${FIND_OPTS[@]}" | grep -v "doc/tutorial.v" | scripts/module-toc-order.py ) -o Makefile

# Patch HTML target to switch out color, and 
# so that it parses comments and has links to ssreflect.
# Also include Makefile.coqdocjs for 'htmlpretty' documentation target.
patch -s < scripts/Makefile.patch
