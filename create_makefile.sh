#!/bin/bash 

# options passed to `find` for locating relevant source files
FIND_OPTS=( . -name '*.v' ! -name '*#*' ! -path './.git/*' ! -path './with-proof-state/*' )

while ! [ -z "$1" ]
do
    case "$1" in
        --without-classic)
            FIND_OPTS+=( ! -path './classic/*' )
            ;;
        --only-classic)
            FIND_OPTS+=( ! -path './analysis/*' ! -path './behavior/*' ! -path './model/*'  ! -path './results/*')
            ;;
        *)
            echo "Unrecognized option: $1"
            exit 1
            ;;
    esac
    shift
done

FIND_OPTS+=( -print )

# Compile all relevant *.v files
coq_makefile -f _CoqProject $(find "${FIND_OPTS[@]}" | scripts/module-toc-order.py ) -o Makefile

# Patch HTML target to switch out color, and 
# so that it parses comments and has links to ssreflect.
# Also include Makefile.coqdocjs for 'htmlpretty' documentation target.
patch -s < scripts/Makefile.patch
