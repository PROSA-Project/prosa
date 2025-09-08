#!/bin/bash

function die {
	echo "Error: $*"
	exit 1
}

# see https://datasette.io/tools/llm
[ -z "$LLM" ] && LLM="llm"

which "$LLM" > /dev/null || die "cannot find $LLM utility."

# by default, use an ollama model
[ -z "$MODEL" ] && MODEL="gpt-oss"

MODEL_AVAILABLE=$("$LLM" models | grep "$MODEL")

[ -z "$MODEL_AVAILABLE" ] && die "model '$MODEL' not found"

PROMPT="Find and report ALL spelling and grammar mistakes.
Ignore spacing.
Do NOT comment on stylistic issues.
Say nothing if there are no serious mistakes."

exec "$LLM" -s "$PROMPT" -m "$MODEL"
