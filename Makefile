# Makefile for Prosa

COQ_PROJ := _CoqProject
COQ_MAKEFILE := Makefile.coq
FIND_OPTS := . -name '*.v' ! -name '*\#*' ! -path './.git/*' ! -path './with-proof-state/*'

default: prosa

all: allCoqProject
	$(MAKE) $(COQ_MAKEFILE)
	$(MAKE) -f $(COQ_MAKEFILE)

prosa: prosaCoqProject
	$(MAKE) $(COQ_MAKEFILE)
	$(MAKE) -f $(COQ_MAKEFILE)

refinements: refinementsCoqProject
	$(MAKE) $(COQ_MAKEFILE)
	$(MAKE) -f $(COQ_MAKEFILE)

commonCoqProject:
	@$(RM) -f $(COQ_PROJ)
	@echo "# Automatically created by make, do not edit" > $(COQ_PROJ)
	@echo "# (edit Makefile instead)" >> $(COQ_PROJ)
	@echo "" >> $(COQ_PROJ)
	@echo "-arg \"-w -notation-overriden,-parsing,-projection-no-head-constant\"" >> $(COQ_PROJ)
	@echo "" >> $(COQ_PROJ)

allCoqProject: commonCoqProject
	@echo "-R . prosa" >> $(COQ_PROJ)
	@echo "" >> $(COQ_PROJ)
	@find $(FIND_OPTS) \
	  -print | scripts/module-toc-order.py >> $(COQ_PROJ)

prosaCoqProject: commonCoqProject
	@echo "-R . prosa" >> $(COQ_PROJ)
	@echo "" >> $(COQ_PROJ)
	@find $(FIND_OPTS) \
	  ! -path './implementation/refinements/*' \
	  -print | scripts/module-toc-order.py >> $(COQ_PROJ)

refinementsCoqProject: commonCoqProject
	@echo "-R implementation/refinements prosa.implementation.refinements" >> $(COQ_PROJ)
	@echo "" >> $(COQ_PROJ)
	@find $(FIND_OPTS) \
	  -path './implementation/refinements/*' \
	  -print | scripts/module-toc-order.py >> $(COQ_PROJ)

$(COQ_MAKEFILE): $(COQ_PROJ) scripts/Makefile.coq.patch
	@coq_makefile -f $< -o $@
	@# Patch HTML target to switch out color, and 
	@# so that it parses comments and has links to ssreflect.
	@# Also include Makefile.coqdocjs for 'htmlpretty' documentation target.
	@patch -s < scripts/Makefile.coq.patch

install html gallinahtml htmlpretty clean cleanall validate alectryon: $(COQ_MAKEFILE)
	$(MAKE) -f $(COQ_MAKEFILE) $@

%.vo: %.v
	$(MAKE) -f $(COQ_MAKEFILE) $@

vacuum: cleanall
	@echo 'VACUUMING *.vo *.glob .*.aux <empty directories>'
	@find . -depth \( -iname '*.vo' -or  -iname '*.glob' -or -iname '.*.aux' \)  ! -path './.git/*' -delete
	@find . -depth -type d -empty ! -path './.git/*' -delete

macos-clean:
	@echo 'CLEAN .DS_Store'
	@find . -depth -iname '.DS_Store' ! -path './.git/*' -delete

spell:
	./scripts/flag-typos-in-comments.sh `find .  -iname '*.v'`

distclean: cleanall
	$(RM) $(COQ_PROJ)

help:
	@echo "You can run:"
	@echo "'make' or 'make prosa' to build Prosa main development"
	@echo "'make refinements' to build the refinement part only"
	@echo "    (requires the main development to be installed)"
	@echo "'make all' to build everything"
	@echo "'make install' to install previously compiled files"
	@echo "'make htmlpretty' to build the documentation based on CoqdocJS"
	@echo "    (can hide/show proofs)"
	@echo "'make gallinahtml' to build the documentation without proofs"
	@echo "'make html' to build the documentation with all proofs"
	@echo "'make clean' to remove generated files"
	@echo "'make vacumm' to clean .vo .glob .aux files and empty dirs"
	@echo "'make macos-clean' to clean macos' .DS_Store dirs"
	@echo "'make distclean' to remove all generated files"

.PHONY: all prosa refinements
.PHONY: commonCoqProject allCoqProject prosaCoqProject refinementsCoqProject
.PHONY: install html gallinahtml htmlpretty clean cleanall validate alectryon
.PHONY: vacuum macos-clean spell distclean help
