#!/usr/bin/env python3

# Copyright 2019 Björn Brandenburg <bbb@mpi-sws.org>
#
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions are met:
#
# 1. Redistributions of source code must retain the above copyright notice, this
# list of conditions and the following disclaimer.
#
# 2. Redistributions in binary form must reproduce the above copyright notice,
# this list of conditions and the following disclaimer in the documentation
# and/or other materials provided with the distribution.
#
# THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
# AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
# IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
# DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
# FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
# DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
# SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
# CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
# OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
# OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

import argparse
import os
import sys
import json

SEP_TOP = "[ coqtop ]".center(77, '-')
SEP_BOTTOM= "-" * 77

def intersperse(src, proofstate, out):
    last = None
    for interaction in proofstate:
        if 'start' in interaction and 'end' in interaction:
            assert type(interaction['start']) == int
            assert type(interaction['end']) == int
            assert interaction['start'] < len(src)
            assert interaction['end'] <= len(src)
            start = interaction['start']
            end = min(interaction['end'] + 1, len(src))
            input = src[start:end]
            print(input, end='', file=out)
            last = end
        if 'output' in interaction:
            print("\n(* %s\n" % SEP_TOP, file=out)
            for line in interaction['output']:
                print(line, file=out)
            print("\n%s *)\n" % SEP_BOTTOM, file=out)

    if not last is None and last + 1 < len(src):
        # print trailing leftovers of file
        input = src[last + 1:]
        print(input, end='', file=out)

def process(opts, fname):
    print("Interspersing proof state in %s..." % fname)

    # read the source
    src = open(fname, 'r').read()

    # load the proof state
    ext = '.proofstate.json'
    proofstate_fname = os.path.join(opts.proof_state_prefix,
                                    fname.replace('.v', ext))
    proofstate = json.load(open(proofstate_fname, 'r'))

    # create the output file
    output_file = os.path.join(opts.output_prefix, fname)
    path = os.path.dirname(output_file)
    os.makedirs(path, exist_ok=True)
    out = open(output_file, 'w')

    intersperse(src, proofstate, out)


def parse_args():
    parser = argparse.ArgumentParser(
        description="intersperse recorded proof state with Coq source")

    parser.add_argument('input_files', nargs='*',
        metavar='Coq-file',
        help='input Coq files (*.v)')

    parser.add_argument('-o', '--output-prefix', default="./with-proof-state",
                        action='store', type=str,
                        help='path prefix for output file(s)')

    parser.add_argument('-p', '--proof-state-prefix', default="./proof-state",
                        action='store', type=str,
                        help='where to find the *.proofstate.json files')

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
