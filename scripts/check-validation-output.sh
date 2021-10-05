#!/bin/sh
set -e

RESULTS="$1"

[ -e "$RESULTS" ] || exit 2

OBSERVED="/tmp/observed-validation-output"
EXPECTED="/tmp/expected-validation-output"

# strip the list of files and COQDEP output
grep -v 'COQDEP VFILES' "$RESULTS" | grep -v '"coqchk" -silent' > "$OBSERVED"

cat > $EXPECTED <<EOF

CONTEXT SUMMARY
===============

* Theory: Set is predicative
  
* Axioms: <none>
  
* Constants/Inductives relying on type-in-type: <none>
  
* Constants/Inductives relying on unsafe (co)fixpoints: <none>
  
* Inductives whose positivity is assumed: <none>
  
EOF

if ! diff --brief "$OBSERVED" "$EXPECTED" > /dev/null
then
    echo "[!!] Validation output does not match expected output."
    echo "[II] Trying workaround for https://github.com/coq/coq/issues/13324"

    # strip the list of files, COQDEP output, and 
    # filter bogus ltac: axioms (see Coq issue 13324)
    grep -v 'COQDEP VFILES' "$RESULTS" | grep -v '"coqchk" -silent' | grep -v "ltac_gen_subproof" > "$OBSERVED"
    # the list of axioms should now be an empty list
    cat > $EXPECTED <<EOF

CONTEXT SUMMARY
===============

* Theory: Set is predicative
  
* Axioms:
  
* Constants/Inductives relying on type-in-type: <none>
  
* Constants/Inductives relying on unsafe (co)fixpoints: <none>
  
* Inductives whose positivity is assumed: <none>
  
EOF
    if ! diff --brief "$OBSERVED" "$EXPECTED" > /dev/null
    then
        echo "[!!] Validation output still does not match expected output."
        diff -u "$OBSERVED" "$EXPECTED"
        exit 3
    fi
fi

# if we get here, we saw the expected output
echo "[II] Validation succeeded."
exit 0
