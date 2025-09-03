#!/bin/bash

# see https://datasette.io/tools/llm
LLM="llm"

# requires ollama
MODEL="gpt-oss"

PROMPT="Find and report all spelling and grammar mistakes.
Ignore spacing.
Do NOT comment on stylistic issues.
Say nothing if there are no serious mistakes."

exec "$LLM" -s "$PROMPT" -m "$MODEL"
