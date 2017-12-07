#!/bin/bash 

# Include rt-proofs library in _CoqProject. (For Coq versions >= 8.6, remove spurious warnings.)
version=$(echo $(coqc -v 1) | grep -o "version .\.." | tail -c 4)
if ([ "$version" == "8.4" ] || [ "$version" == "8.5" ]) then
  echo "-R . rt" > _CoqProject
else
  echo -R . rt -arg \"-w -notation-overriden,-parsing\" > _CoqProject
fi

# Compile all *.v files (except the ones that define the decidable equality). Those
# are directly included in other files.
coq_makefile -f _CoqProject $(find . -name "*.v" ! -name "*#*" ! -name "*eqdec*.v" -print) -o Makefile

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
	sed -i '' 's|-interpolate -utf8|-interpolate -utf8 --plain-comments --parse-comments --external https://math-comp.github.io/math-comp/htmldoc/ mathcomp|g' Makefile
else
	sed -i 's|-interpolate -utf8|-interpolate -utf8 --plain-comments --parse-comments --external https://math-comp.github.io/math-comp/htmldoc/ mathcomp|g' Makefile
fi

# Fix 'make clean' to remove all binary files, regardless of name
if [ "$(uname)" == "Darwin" ]; then
	sed -i '' 's|rm -f $(VOFILES) $(VOFILES:.vo=.vio) $(GFILES) $(VFILES:.v=.v.d) $(VFILES:=.beautified) $(VFILES:=.old)|find . -name "*.vo" -delete -o -name "*.glob" -delete -o -name "*.v.d" -delete -o -name "*.vio" -delete -o -name "*.old" -delete -o -name "*.beautified" -delete|g' Makefile
else
	sed -i 's|rm -f $(VOFILES) $(VOFILES:.vo=.vio) $(GFILES) $(VFILES:.v=.v.d) $(VFILES:=.beautified) $(VFILES:=.old)|find . -name "*.vo" -delete -o -name "*.glob" -delete -o -name "*.v.d" -delete -o -name "*.vio" -delete -o -name "*.old" -delete -o -name "*.beautified" -delete|g' Makefile
fi

