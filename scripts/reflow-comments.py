#!/usr/bin/env python3

import argparse
import contextlib
import sys
import re
from pathlib import Path

from comments import comment_ranges


def reflow_comments(src, max_cols=80, strict_at_end=False, dump_tokens=False):
    def atomic_tokens(start, end):
        last = start
        empty = True
        newlines = 0
        inline_code = 0
        verbatim = 0
        raw_html = 0
        for pos in range(start, end):
            c = src[pos]
            if c.isspace():
                if empty:
                    last += 1
                elif not inline_code and not verbatim and not raw_html:
                    if newlines > 1 or (newlines == 1 and src[last:pos] == "-"):
                        yield (last, last)
                    yield (last, pos)
                    last = pos + 1
                    empty = True
                    newlines = 0
                if c == "\n":
                    newlines += 1
            else:
                empty = False
            if c == "<" and not verbatim and not inline_code:
                if src[pos : min(pos + 2, end)] == "<<":
                    verbatim += 1
            if c == ">" and verbatim:
                if src[pos : min(pos + 2, end)] == ">>":
                    verbatim -= 1
            if c == "[" and not verbatim:
                inline_code += 1
            if c == "]" and inline_code and not verbatim:
                inline_code -= 1
            if c == "#" and raw_html:
                raw_html -= 1
            elif c == "#" and not verbatim and not inline_code:
                raw_html += 1

        if not empty:
            yield (last, end)

    # works for spaces only
    def indentation(pos):
        i = 0
        for i, c in enumerate(reversed(src[:pos])):
            if c == "\n":
                break
        return i

    def first_line_space(start, end):
        pos = start
        for pos in range(start, end):
            if not src[pos].isspace():
                break
        return pos - start

    def is_bullet(pos, end):
        return src[pos] == "-" and pos + 1 == end

    def reflow(start, end):
        indent = None
        cursor = 0
        first_line = first_line_space(start, end)
        for a, b in atomic_tokens(start, end):
            if a == b:
                # new paragraph
                indent = None
                cursor = 0
                print("\n\n", end="")
            else:
                token = src[a:b]
                if not (token.startswith("<<") and token.endswith(">>")):
                    # normalize any contained whitespace
                    token = re.sub(r"\s+", " ", token)
                if indent is None:
                    indent = indentation(a)
                    if first_line is not None:
                        print(" " * first_line, end="")
                        print(token, end="")
                        first_line = None
                    else:
                        print(" " * indent, end="")
                        print(token, end="")
                    cursor += indent + b - a
                    if is_bullet(a, b):
                        indent += 2
                elif cursor + (b - a + 1) <= max_cols:
                    print(" ", end="")
                    print(token, end="")
                    cursor += b - a + 1
                else:
                    print("\n" + (" " * indent), end="")
                    print(token, end="")
                    cursor = indent + b - a
        if cursor + 3 <= max_cols or not strict_at_end:
            print(" ", end="")
        elif indent is not None:
            print("\n" + (" " * indent), end="")

    pos = 0
    for start, end in comment_ranges(src):
        print(src[pos:start], end="")
        reflow(start, end)
        pos = end
    print(src[pos:], end="")
    if src[-1] != "\n":
        print()

    if dump_tokens:
        for start, end in comment_ranges(src):
            print("\n" + ("=" * 80))
            print(start, end)
            print(src[start:end])
            for a, b in atomic_tokens(start, end):
                if a == b:
                    print("- PARAGRAPH BREAK")
                else:
                    print(f"- {a}-{b}: {src[a:b]}")
            print("->")
            reflow(start, end)


def process(opts, fpath):
    with fpath.open() as f:
        src = f.read()
    if opts.in_place:
        with fpath.open("w") as f:
            with contextlib.redirect_stdout(f):
                reflow_comments(
                    src,
                    max_cols=opts.max_columns,
                    strict_at_end=opts.strict_closing_delimiter,
                )
    else:
        reflow_comments(
            src, max_cols=opts.max_columns, strict_at_end=opts.strict_closing_delimiter
        )


def parse_args():
    parser = argparse.ArgumentParser(description="reformat comments in Gallina files")

    parser.add_argument(
        "input_files",
        nargs="*",
        type=Path,
        metavar="Gallina-file",
        help="input Gallina files (*.v)",
    )
    parser.add_argument(
        "--max-columns",
        action="store",
        default=72,
        type=int,
        help="Maximum permitted line length (in characters, default: 72)",
    )
    parser.add_argument(
        "--in-place",
        action="store_true",
        help="Perform the update in place (overwrite source files)",
    )
    parser.add_argument(
        "--strict-closing-delimiter",
        action="store_true",
        help="Don't allow the closing '*)' to spill beyond --max-columns.",
    )

    return parser.parse_args()


def main():
    opts = parse_args()

    had_problem = False
    for f in opts.input_files:
        try:
            process(opts, f)
        except OSError as e:
            print(e, file=sys.stderr)
            had_problem = True

    if had_problem:
        sys.exit(1)


if __name__ == "__main__":
    main()
