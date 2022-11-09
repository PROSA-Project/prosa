#!/bin/sh
set -e

ALE="python3 ./scripts/alectryon_custom_driver.py"
OUT="./html-alectryon"

mkdir -p "$OUT"

for F in $*
do
    HTML=`echo "prosa/$F" | sed -e sX[.]/XX -e s/[.]v/.html/ | tr / .`
    echo $F '->' $HTML
    $ALE -R . prosa --output-directory "$OUT" --output "$OUT/$HTML" --backend webpage --frontend coq $F
done
