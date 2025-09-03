#!/bin/bash

function check_one_file {
    FILE="$1"
    MOD="${FILE//\//.}"
    MOD="prosa.${MOD/.v/}"

    THEOREMS=$(grep -E '^ *Theorem [^ ]+ *:' "$FILE" | sed -e 's/^ *Theorem//' -e 's/ *:.*$//')
    for THM in $THEOREMS
    do
        OUTPUT=$(mktemp)
        (
            echo "Require ${MOD}."
            echo "Print Assumptions ${MOD}.${THM}."
        ) \
        | coqtop -nois -R . prosa > "$OUTPUT" 2>&1 || exit 2
        if grep -q "Closed under the global context" "$OUTPUT"
        then
            echo "OK ${MOD}.${THM}"
        else
            echo "FAIL ${MOD}.${THM}"
            cat "$OUTPUT"
            exit 1
        fi
        rm "$OUTPUT"
    done
}


while [ -n "$1" ]
do
    if [ -d "$1" ]
    then
        for F in $(find "$1" -iname '*.v')
        do
            check_one_file "$F" || exit 1
        done
    else
        check_one_file "$1" || exit 1
    fi
    shift
done
