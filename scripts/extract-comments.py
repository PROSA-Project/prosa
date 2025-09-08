#!/usr/bin/env python3

import argparse
import re
import sys

INLINE_CODE_RE = re.compile(r"\[[^]]*?\]")
INLINE_HTML_RE = re.compile(r"#[^#]*?#")
WHITESPACE_RE = re.compile(r"\s+")


def comment_ranges(src):
    "Identify comments in Coq .v files."

    def cur_is(i, c):
        return src[i] == c

    def next_is(i, c):
        if i + 1 < len(src):
            return src[i + 1] == c
        else:
            return False

    in_comment = 0
    comment_start = None

    # limitation: doesn't do anything smart about nested comments for now
    for i in range(len(src)):
        assert in_comment >= 0
        # comment starting?
        if cur_is(i, "(") and next_is(i, "*"):
            in_comment += 1
            if in_comment == 1:
                if next_is(i + 1, "*"):
                    comment_start = i + 3
                else:
                    comment_start = i + 2
        # comment ending?
        elif cur_is(i, "*") and next_is(i, ")"):
            in_comment -= 1
            if in_comment == 0:
                yield (comment_start, i)


def process(opts, fname):
    src = open(fname, "r").read()
    if opts.merge_dots:
        if opts.keep_inline:
            comments = [src[a:b].strip() for (a, b) in comment_ranges(src)]
        else:
            comments = [
                INLINE_CODE_RE.sub("", src[a:b].strip())
                for (a, b) in comment_ranges(src)
            ]
        comments = [INLINE_HTML_RE.sub("", c) for c in comments]
        if opts.single_line:
            comments = [WHITESPACE_RE.sub(" ", c) for c in comments]
        merged_comments = []
        for c in comments:
            if not merged_comments:
                merged_comments.append(c)
            if merged_comments[-1].endswith("...") and c.startswith("..."):
                merged_comments[-1] = f"{merged_comments[-1][:-3]}{c[3:]}"
            else:
                merged_comments.append(c)

        for c in merged_comments:
            print(c)
    else:
        for a, b in comment_ranges(src):
            txt = src[a:b]
            if opts.single_line:
                txt = WHITESPACE_RE.sub(" ", txt)
            if opts.keep_inline:
                print(INLINE_HTML_RE.sub("", txt))
            else:
                print(INLINE_HTML_RE.sub("", INLINE_CODE_RE.sub("", txt)))


def parse_args():
    parser = argparse.ArgumentParser(description="extract comments from Gallina files")

    parser.add_argument(
        "input_files",
        nargs="*",
        metavar="Gallina-file",
        help="input Gallina files (*.v)",
    )
    parser.add_argument(
        "--keep-inline",
        action="store_true",
        help="Do not strip inline code from comments",
    )
    parser.add_argument(
        "--merge-dots",
        action="store_true",
        help='Merge continued comments follwing the "..." pattern.',
    )
    parser.add_argument(
        "--single-line",
        action="store_true",
        help="Emit one comment per line",
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
        # signal something went wrong with non-zero exit code
        sys.exit(1)


if __name__ == "__main__":
    main()
