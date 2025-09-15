#!/usr/bin/env python3

import argparse
import os
import re
import subprocess
import sys
from pathlib import Path

from comments import Comments, LineNumbers

ISSUES = [
    (re.compile(regex, re.MULTILINE | re.DOTALL), msg, adjust_edit_offset)
    for msg, regex, adjust_edit_offset in [
        (
            "missing space before ':='",
            r"(Lemma|Theorem|Fact|Corollary|Remark|Definition|Fixpoint)\s+[^.]*?(\S:=)[^.]*?\.",
            1,
        ),
        (
            "missing space after ':='",
            r"(Lemma|Theorem|Fact|Corollary|Remark|Definition|Fixpoint)\s+[^.]*?(:=\S)[^.]*?\.",
            2,
        ),
        (
            "missing space before ':'",
            r"(Hypothesis|Variable|Variables|Instance|Context)\s+[^.]*?(\S:)\s[^.]*?\.",
            1,
        ),
        (
            "missing space after ':'",
            r"(Hypothesis|Variable|Variables|Instance|Context)\s+[^.]*?([^. \n]:[^= \n])[^.]*?\.",
            2,
        ),
        (
            "missing space before ':'",
            r"(Lemma|Theorem|Fact|Corollary|Remark|Definition|Fixpoint)\s+[^.]*?(\S:)\s[^.]*?(:=)?[^.]*?\.",
            1,
        ),
        (
            "missing space after ':'",
            r"(Lemma|Theorem|Fact|Corollary|Remark|Definition|Fixpoint)\s+[^.]*?(:[^= \n])[^.]*?:=[^.]*?\.",
            1,
        ),
    ]
]

EXCEPTIONS = [
    r"%:R",  # MathComp syntax for nat -> ring coercion
    ("", r"[::", "]"),  # MathComp empty list notation
    (" ", "::", " "),  # cons notation
    ("[", "::", " "),  # singleton list notation
]


def is_excepted(m):
    for e in EXCEPTIONS:
        if isinstance(e, str):
            if m[2] == e:
                return True
        elif isinstance(e, tuple):
            prefix, match, suffix = e
            if m[2] != match:
                continue
            s, e = m.span(2)
            if prefix != m.string[s - len(prefix) : s]:
                continue
            if suffix == m.string[e : e + len(suffix)]:
                return True

    return False


def lint_file(opts, fpath):
    issues = []

    with fpath.open() as f:
        src = f.read()

    comments = Comments(src)
    lineno = LineNumbers(src)

    def violations_of(regex):
        return (m for m in regex.finditer(src) if m.span() not in comments)

    for i, (rule, msg, shift) in enumerate(ISSUES):
        for m in violations_of(rule):
            if is_excepted(m):
                continue
            rule = f" [rule: {i + 1}]" if opts.show_rule_number else ""
            issues.append(
                (
                    m.span(2),
                    f"{fpath}:{lineno[m.span(2)[0]]}: coding style{rule}: {msg}",
                    shift,
                )
            )

    for i, ((s, e), msg, offset_shift) in enumerate(sorted(issues)):
        print(msg, file=sys.stderr)
        if opts.explain:
            line = lineno.line_for_offset(s)
            indent = "  "
            print(f"\n{indent}{line}", end="", file=sys.stderr)
            space = " " * lineno.offset_within_line(s)
            marker = "^" * (e - s)
            print(f"{indent}{space}{marker}\n", file=sys.stderr)

        if opts.open_editor:
            cmd = (
                opts.open_editor.replace("$EDITOR", os.getenv("EDITOR", "emacsclient"))
                .replace("$FILE", str(fpath))
                .replace("$LINE", str(lineno[s]))
                .replace(
                    "$OFFSET", str(1 + lineno.offset_within_line(s) + offset_shift)
                )
            )
            try:
                print(f"-> opening editor by running: {cmd} ...")
                subprocess.run(cmd, shell=True, check=True)
            except subprocess.CalledProcessError as e:
                print("Error: failed to launch {cmd}: {e}", file=sys.stderr)

        if opts.max_issues_per_file is not None and i + 1 >= opts.max_issues_per_file:
            break

    return len(issues)


DEFAULT_OPEN_EDITOR_CMD = "$EDITOR +$LINE:$OFFSET $FILE"


def parse_args():
    parser = argparse.ArgumentParser(
        description="check for common Prosa coding style violations"
    )

    parser.add_argument(
        "input_files",
        nargs="*",
        type=Path,
        metavar="Gallina-file",
        help="input Gallina files (*.v)",
    )

    parser.add_argument(
        "-r",
        "--show-rule-number",
        action="store_true",
        help="State which rule is being violated.",
    )

    parser.add_argument(
        "-e",
        "--explain",
        action="store_true",
        help="Illustrate the issue.",
    )

    parser.add_argument(
        "-o",
        "--open-editor",
        action="store",
        nargs="?",
        metavar="COMMAND",
        const=DEFAULT_OPEN_EDITOR_CMD,
        help=f"open the file in an editor with the given command (default: {DEFAULT_OPEN_EDITOR_CMD})",
    )

    parser.add_argument(
        "-m",
        "--max-issues-per-file",
        action="store",
        nargs="?",
        metavar="N",
        type=int,
        const=1,
        help="Report at most N issues per file (default: 1).",
    )

    return parser.parse_args()


def main():
    opts = parse_args()

    issues = 0
    for f in opts.input_files:
        try:
            issues += lint_file(opts, f)
        except OSError as e:
            print(e, file=sys.stderr)
            issues += 1

    sys.exit(issues > 0)


if __name__ == "__main__":
    main()
