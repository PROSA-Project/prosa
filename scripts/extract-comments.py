#!/usr/bin/env python3

import argparse
import sys
import os
import re

INLINE_CODE_RE = re.compile(r'\[[^]]*?\]')

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
        if cur_is(i, '(') and next_is(i, '*'):
            in_comment += 1
            if in_comment == 1:
                comment_start = i + 2
        # comment ending?
        elif cur_is(i, '*') and next_is(i, ')'):
            in_comment -= 1
            if in_comment == 0:
                yield (comment_start, i)


def process(opts, fname):
    src = open(fname, 'r').read()
    out = sys.stdout
    for (a, b) in comment_ranges(src):
        txt = src[a:b]
        print(INLINE_CODE_RE.sub('', txt))
#     out.close()

def parse_args():
    parser = argparse.ArgumentParser(
        description="extract comments from Gallina files")

    parser.add_argument('input_files', nargs='*',
        metavar='Gallina-file',
        help='input Gallina files (*.v)')

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

if __name__ == '__main__':
    main()

