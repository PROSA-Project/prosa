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
            r"(Lemma|Theorem|Fact|Corollary|Remark|Definition|Fixpoint)\s+[^.]*?(?P<issue>\S:=)[^.]*?\.",
            1,
        ),
        (
            "missing space after ':='",
            r"(Lemma|Theorem|Fact|Corollary|Remark|Definition|Fixpoint)\s+[^.]*?(?P<issue>:=\S)[^.]*?\.",
            2,
        ),
        (
            "missing space before ':'",
            r"(Hypothesis|Variable|Variables|Instance|Context)\s+[^.]*?(?P<issue>\S:)\s[^.]*?\.",
            1,
        ),
        (
            "missing space after ':'",
            r"(Hypothesis|Variable|Variables|Instance|Context)\s+[^.]*?(?P<issue>[^. \n]:[^= \n])[^.]*?\.",
            2,
        ),
        (
            "missing space before ':'",
            r"(Lemma|Theorem|Fact|Corollary|Remark|Definition|Fixpoint)\s+[^.]*?(?P<issue>\S:)\s[^.]*?(:=)?[^.]*?\.",
            1,
        ),
        (
            "missing space after ':'",
            r"(Lemma|Theorem|Fact|Corollary|Remark|Definition|Fixpoint)\s+[^.]*?(?P<issue>:[^= \n])[^.]*?:=[^.]*?\.",
            1,
        ),
        ("trailing whitespace", r"(?P<issue>[ \t]+)\n", 0),
        (
            "operator at end of line (move to next line)",
            r"\s(?P<issue>[-+*/\\=!&|]+)\n",
            0,
        ),
    ]
]

EXCEPTIONS = [
    r"%:R",  # MathComp syntax for nat -> ring coercion
    ("", r"[::", "]"),  # MathComp empty list notation
    (" ", "::", " "),  # cons notation
    ("[", "::", " "),  # singleton list notation
    (" ", "//", "\n"),  # proof-mode '//'
    (" ", "//=", "\n"),  # proof-mode '//='
]


def is_excepted(m):
    for e in EXCEPTIONS:
        if isinstance(e, str):
            if m["issue"] == e:
                return True
        elif isinstance(e, tuple):
            prefix, match, suffix = e
            if m["issue"] != match:
                continue
            s, e = m.span("issue")
            if prefix != m.string[s - len(prefix) : s]:
                continue
            if suffix == m.string[e : e + len(suffix)]:
                return True

    return False


KEYWORDS_FOR_INDENTATION_CHECK = re.compile(
    r"(?P<section>Section|End)\s+[a-zA-Z_]+.|^\s+(?P<kw>Lemma|Theorem|Fact|Corollary|Remark|Definition|Fixpoint|Hypothesis|"
    r"Variable|Variables|Instance|Context|Global|Local|Proof|Qed|Defined|Aborted|Admitted)",
    re.MULTILINE | re.DOTALL,
)

QUANTIFIER_FOR_INDENTATION_CHECK = re.compile(
    r"\s+(?P<quantifier>forall|exists)[^,\n]+,(?P<stacked>[ ]*(forall|exists)[^,\n]+,)*\n\s*(?P<nline>[^ \n]+)",
    re.MULTILINE | re.DOTALL,
)

INDENT_SPACES = 2


def lint_file(opts, fpath):
    issues = []

    with fpath.open() as f:
        src = f.read()

    comments = Comments(src)
    lineno = LineNumbers(src)

    def matches_of(regex):
        return (m for m in regex.finditer(src) if m.span() not in comments)

    for i, (rule, msg, shift) in enumerate(ISSUES):
        for m in matches_of(rule):
            if is_excepted(m):
                continue
            rule = f" [rule: {i + 1}]" if opts.show_rule_number else ""
            issues.append(
                (
                    m.span("issue"),
                    f"{fpath}:{lineno[m.span('issue')[0]]}: coding style{rule}: {msg}",
                    shift,
                    0,
                )
            )

    expected_indent = 0
    for m in matches_of(KEYWORDS_FOR_INDENTATION_CHECK):
        s, e = m.span("section")
        if s == -1:
            s, e = m.span("kw")

        if src[s:e] == "End":
            expected_indent -= INDENT_SPACES

        indentation = lineno.offset_within_line(s)
        if indentation != expected_indent:
            issues.append(
                (
                    (s, e),
                    f"{fpath}:{lineno[s]}: bad indentation (expected {expected_indent}, found {indentation})",
                    0,
                    0,
                )
            )
        if src[s:e] == "Section":
            expected_indent += INDENT_SPACES
        assert expected_indent >= 0

    for m in matches_of(QUANTIFIER_FOR_INDENTATION_CHECK):
        quantifier_indentation = lineno.offset_within_line(m.span("quantifier")[0])
        expression_indentation = lineno.offset_within_line(m.span("nline")[0])
        if quantifier_indentation + INDENT_SPACES != expression_indentation:
            issues.append(
                (
                    m.span("nline"),
                    f"{fpath}:{lineno[m.span('nline')[0]]}: bad indentation after "
                    f"{m.group('quantifier')} (expected {quantifier_indentation + INDENT_SPACES}, "
                    f"found {expression_indentation})",
                    0,
                    1,
                )
            )

    for i, ((s, e), msg, offset_shift, context_above) in enumerate(sorted(issues)):
        print(msg, file=sys.stderr)
        if opts.explain:
            indent = "  "
            ln = lineno[s]
            print(file=sys.stderr)
            for k in range(max(0, ln - context_above), ln + 1):
                print(f"{indent}{lineno.line(k)}", end="", file=sys.stderr)
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
