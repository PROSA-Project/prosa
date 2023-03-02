#!/bin/sh

EXIT=0

KNOWN_EXCEPTIONS=./scripts/wordlist.pws

while ! [ -z "$1" ]
do
	MD="$1"
		
	for WORD in $(cat "$1" \
	    | aspell --mode=markdown --add-extra-dicts=$KNOWN_EXCEPTIONS -l en list \
		| sort \
		| uniq)
	do
		echo "$MD: potentially misspelled word '$WORD'"
		EXIT=1
	done
	shift
done
exit $EXIT
