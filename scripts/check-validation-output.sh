#!/bin/sh
set -e

while ! [ -z "$1" ]
do
    case "$1" in
        --accept-proof-irrelevance)
            ACCEPT_PI=1
            ;;
        -*)
            echo "Unrecognized option: $1"
            exit 1
            ;;
        *)
        	RESULTS="$1"
        	;;
    esac
    shift
done

[ -e "$RESULTS" ] || exit 2

OBSERVED="/tmp/observed-validation-output"
EXPECTED="/tmp/expected-validation-output"

# strip the list of files and COQDEP output
grep -v 'COQDEP VFILES' "$RESULTS" | grep -v 'make' | grep -v '"coqchk" -silent' > "$OBSERVED"

if [ -z "$ACCEPT_PI" ]
then
	cat > $EXPECTED <<EOF

CONTEXT SUMMARY
===============

* Theory: Set is predicative
  
* Axioms: <none>
  
* Constants/Inductives relying on type-in-type: <none>
  
* Constants/Inductives relying on unsafe (co)fixpoints: <none>
  
* Inductives whose positivity is assumed: <none>
  
EOF
else
	cat > $EXPECTED <<EOF

CONTEXT SUMMARY
===============

* Theory: Set is predicative
  
* Axioms:
    Coq.Logic.ProofIrrelevance.proof_irrelevance
  
* Constants/Inductives relying on type-in-type: <none>
  
* Constants/Inductives relying on unsafe (co)fixpoints: <none>
  
* Inductives whose positivity is assumed: <none>
  
EOF
fi

if ! diff --brief "$EXPECTED" "$OBSERVED"  > /dev/null
then
    echo "[!!] Validation output does not match expected output."
    echo "[II] Trying workaround for https://github.com/coq/coq/issues/13324"

    # strip the list of files, COQDEP output, and 
    # filter bogus ltac: axioms (see Coq issue 13324)
    grep -v 'COQDEP VFILES' "$RESULTS" | grep -v 'make' | grep -v '"coqchk" -silent' | grep -v "ltac_gen_subproof" > "$OBSERVED"
    # the list of axioms should now be an empty list
    if ! diff --brief  "$EXPECTED" "$OBSERVED" > /dev/null
    then
        echo "[!!] Validation output still does not match expected output."
        diff -u  "$EXPECTED" "$OBSERVED"
        exit 3
    fi
fi

# if we get here, we saw the expected output
echo "[II] Validation succeeded."
exit 0
