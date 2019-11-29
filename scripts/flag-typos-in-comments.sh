#!/bin/sh

EXIT=0

KNOWN_EXCEPTIONS=./scripts/wordlist.pws

while ! [ -z "$1" ]
do
	SRC="$1"
	for WORD in $(scripts/extract-comments.py "$SRC" \
		| aspell --add-extra-dicts=$KNOWN_EXCEPTIONS -l en  list \
		| sort \
		| uniq)
	do
		echo "$SRC: potentially misspelled word '$WORD'"
		EXIT=1
	done
	shift
done
exit $EXIT
