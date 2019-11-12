#!/bin/bash 

# options passed to `find` for locating relevant source files
FIND_OPTS=( . -name '*.v' ! -name '*#*' ! -path './.git/*' )

while ! [ -z "$1" ]
do
    case "$1" in
        --without-classic)
            FIND_OPTS+=( ! -path './classic/*' )
            ;;
        --only-classic)
            FIND_OPTS+=( ! -path './restructuring/*' )
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
coq_makefile -f _CoqProject $(find "${FIND_OPTS[@]}" ) -o Makefile

# Fix the 'make validate' command. It doesn't handle the library prefix properly
# and cause clashes for files with the same name. This forces full filenames and
# adds the rt. prefix
if [ "$(uname)" == "Darwin" ]; then
	sed -i '' 's|$(notdir $(^:.vo=))|$(addprefix rt., $(subst /,., $(^:.vo=)))|g' Makefile
else
	sed -i 's|$(notdir $(^:.vo=))|$(addprefix rt., $(subst /,., $(^:.vo=)))|g' Makefile
fi

# Patch Makefile.coqdocjs for pretty documentation targets
printf "\n# Include pretty documentation targets\ninclude scripts/coqdocjs/Makefile.coqdocjs" >> Makefile

# Patch HTML target to switch out color, and 
# so that it parses comments and has links to ssreflect.
patch -s < scripts/Makefile.patch
