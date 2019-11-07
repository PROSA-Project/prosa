#!/bin/bash 

while ! [ -z "$1" ]
do
    case "$1" in
        --without-classic)
            SKIP_CLASSIC=yes
            ;;
        *)
            echo "Unrecognized option: $1"
            exit 1
            ;;
    esac
    shift
done

# Include rt-proofs library in _CoqProject.
# (For Coq versions >= 8.6, remove spurious warnings.)
echo -R . rt -arg \"-w -notation-overriden,-parsing\" > _CoqProject

# Compile all *.v files
if [ "yes" == "$SKIP_CLASSIC" ]
then
    coq_makefile -f _CoqProject $(find . -name "*.v"  ! -name "*#*" ! -path "./.git/*" ! -path "./classic/*" -print) -o Makefile
else
    coq_makefile -f _CoqProject $(find . -name "*.v"  ! -name "*#*" ! -path "./.git/*" -print) -o Makefile
fi

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
