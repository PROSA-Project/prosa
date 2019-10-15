#!/bin/bash 

# Include rt-proofs library in _CoqProject.
# (For Coq versions >= 8.6, remove spurious warnings.)
echo -R . rt -arg \"-w -notation-overriden,-parsing\" > _CoqProject

# Compile all *.v files
coq_makefile -f _CoqProject $(find . -name "*.v"  ! -name "*#*" ! -path "./.git/*" -print) -o Makefile

# Fix the 'make validate' command. It doesn't handle the library prefix properly
# and cause clashes for files with the same name. This forces full filenames and
# adds the rt. prefix
if [ "$(uname)" == "Darwin" ]; then
	sed -i '' 's|$(notdir $(^:.vo=))|$(addprefix rt., $(subst /,., $(^:.vo=)))|g' Makefile
else
	sed -i 's|$(notdir $(^:.vo=))|$(addprefix rt., $(subst /,., $(^:.vo=)))|g' Makefile
fi


# Fix 'make html' so that it parses comments and has links to ssreflect.
if [ "$(uname)" == "Darwin" ]; then
	sed -i '' 's|-interpolate -utf8|--interpolate --utf8 --plain-comments --parse-comments --external https://math-comp.github.io/math-comp/htmldoc/ mathcomp|g' Makefile
else
	sed -i 's|-interpolate -utf8|--interpolate --utf8 --plain-comments --parse-comments --external https://math-comp.github.io/math-comp/htmldoc/ mathcomp|g' Makefile
fi

# Patch Makefile.coqdocjs for pretty documentation targets
printf "\n# Include pretty documentation targets\ninclude scripts/coqdocjs/Makefile.coqdocjs" >> Makefile

# Patch HTML target to switch out color
patch -s < scripts/Makefile.patch
