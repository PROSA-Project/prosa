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
import sys
import os
import re
import time
from subprocess import Popen, PIPE
from select import select

import json

# YAML support is not part of the standard library, so try loading it carefully
try:
    import yaml
    have_yaml = True
except:
    have_yaml = False

def statement_end_offsets(opts, src):
    """A naive splitter for Coq .v files.
    Pays attention to nested comments and considers each period followed
    by whitespace to be the end of something that should be sent to coqtop.

    Returns an iterator over the indices within the src string where
    statements end.
    """
    def cur_is(i, c):
        return src[i] == c

    def next_is(i, c):
        if i + 1 < len(src):
            return src[i + 1] == c
        else:
            return False

    def prev_is(i, c):
        if i > 0:
            return src[i - 1] == c
        else:
            return False

    def next_is_whitespace(i):
        if i + 1 < len(src):
            return src[i + 1].isspace()
        else:
            # For practical purposes, let's count EOF as white space.
            return True

    def prev_is_whitespace(i):
        if i > 0:
            return src[i - 1].isspace()
        else:
            return False

    def cur_is_bullet(i):
        return src[i] in "-+*"

    def only_whitespace_since_newline(i):
        while i > 0:
            i -= 1
            if not src[i].isspace():
                return False
            if src[i] == '\n':
                return True
        return True

    def end_of_bullet(i):
        while i < len(src) and cur_is_bullet(i):
            i += 1
        if i >= len(src):
            return False
        if src[i].isspace():
            return i
        else:
            return False

    def start_of_proof(i):
        return src[:i].endswith("Proof") \
               or src[:i].endswith("Next Obligation")

    in_comment = 0
    in_proof = 0

    def end_of_proof(i):
        return src[:i].endswith("Qed") \
               or (in_proof and src[:i].endswith("Defined"))

    last = -1
    seen_non_whitespace_since_last = False
    i = 0
    while i < len(src):
        comment_just_ended = False
        if opts.parse_only and opts.verbose:
            print("%7d [%s]  comment:%d  proof:%d  ns:%d  nsnl:%d  bullet:%d  last:%d" % (
                i,
                src[i].replace('\n', '\\n'),
                in_comment,
                in_proof,
                seen_non_whitespace_since_last,
                not only_whitespace_since_newline(i),
                cur_is_bullet(i),
                last
            ))
        assert in_comment >= 0
        assert in_proof >= 0
        # comment starting?
        if cur_is(i, '(') and next_is(i, '*'):
            in_comment += 1
            i += 1 # skip next
        # comment ending?
        elif cur_is(i, '*') and next_is(i, ')'):
            in_comment -= 1
            i += 1 # skip next
            comment_just_ended = True
        # look for statements ending in a period
        elif not in_comment and cur_is(i, '.') and next_is_whitespace(i):
            if start_of_proof(i):
                in_proof += 1
            elif end_of_proof(i):
                in_proof -= 1
            yield i + 1
            last = i + 1
        # look for closing braces -- this is a brittle heuristic, but
        # we need to catch sub-proofs because coqtop in emacs mode
        # produces a prompt every time we enter a sub-proof
        elif not in_comment and in_proof and cur_is(i, '}') and \
             (next_is_whitespace(i) or next_is (i, '}')) and \
             (prev_is_whitespace(i) or prev_is(i, '}')):
            if next_is_whitespace(i):
                yield i + 1
                last = i + 1
            else:
                yield i
                last = i
        # similarly, look for opening braces
        elif not in_comment and in_proof and cur_is(i, '{') \
             and next_is_whitespace(i) and prev_is_whitespace(i):
            yield i + 1
            last = i + 1
        # detect bulleted sub-proofs for the same reason
        elif not in_comment and in_proof and cur_is_bullet(i) \
             and only_whitespace_since_newline(i) \
             and not seen_non_whitespace_since_last:
            # bullets can consist of multiple characters
            end = end_of_bullet(i)
            if not end is False:
                yield end
                last = end
                i = end # skip over entire bullet
            # otherwise just skip over this

        # reset flags
        if i == last:
            seen_non_whitespace_since_last = False
        elif not (in_comment or comment_just_ended) and not src[i].isspace():
            seen_non_whitespace_since_last = True
        # advance to next character
        i += 1

def launch_coqtop(opts):
    # Let the shell figure out where coqtop is and resolve the options.
    # A bit naive but works for now.
    return Popen("coqtop -emacs %s" % opts.coqtop_opts, stdin=PIPE, stdout=PIPE,
                 stderr=PIPE, shell=True, bufsize=0)

START_OF_PROMPT = "<prompt>"
END_OF_PROMPT   = "</prompt>"
END_OF_PROMPT_BYTES = bytes(END_OF_PROMPT, 'utf-8')

def read_from_pipe(pipe, timeout, seen_enough = lambda _: False, expect_timeout=False):
    output = bytearray()
    while not seen_enough(output):
        (readable, writable, exceptional) = select([pipe], [], [], timeout)
        if not readable:
            # we timed out, nothing to read
            if timeout > 0:
                if not expect_timeout:
                    print('=' * 30 + "[ TIMEOUT ]" + '=' * 30)
            break
        else:
            data = readable[0].read(512)
            if len(data) == 0:
                # reached end of pipe
                break
            else:
                output += data
    return output.decode("utf-8")

COQ_PROMPT_RE = re.compile(r"<prompt>\S* < ([0-9]+) ")

def wait_for_prompt(opts, pipe, timeout):
    seen_enough = lambda output: output.endswith(END_OF_PROMPT_BYTES)
    output = read_from_pipe(pipe, timeout, seen_enough)

    while True:
        more = read_from_pipe(pipe, 0, seen_enough, expect_timeout=True)
        output += more
        if more:
            print("Unexpected coqtop output:", more)
            assert False # we lost sync; this should not be happening
        else:
            break

    # check for interaction number in output
    m = COQ_PROMPT_RE.search(output)
    prompt_number = int(m.group(1)) if m else -1
    # remove any prompts; we don't want to record those
    if output.endswith(END_OF_PROMPT) and not opts.verbose:
        idx = output.find(START_OF_PROMPT)
        if START_OF_PROMPT in output[idx+1:]:
            print("Unexpected number of prompts in coqtop output: \n", output)
            assert False # only one prompt expected
        return (prompt_number, output[:idx])
    else:
        return (prompt_number, output)

INFO_MSG_PATTERN = re.compile(
r"""
<infomsg>  # Opening tag
(.*?)      # whatever message — don't be greedy to not skip over closing tag
</infomsg> # Closing tag
\n?        # if the message is at the end of a line, remove the newline as well
"""
, re.VERBOSE | re.DOTALL)

def extract_info_messages(output):
    infos = [m.group(1).rstrip() for m in INFO_MSG_PATTERN.finditer(output)]
    rest = INFO_MSG_PATTERN.sub('', output)
    return (infos, rest)

def wait_for_coqtop(opts, coqtop):
    # wait until prompt (re-)appears
    num, error = wait_for_prompt(opts, coqtop.stderr, opts.timeout)
    # read output produced so far
    # FIXME: this only works if all output fits into the OS's pipe buffer
    output = read_from_pipe(coqtop.stdout, 0)
    interaction = {}
    output = output.rstrip()
    if output:
        interaction['output'] = output.split('\n')
    error  = error.rstrip()
    if error:
        interaction['error'] = error
    if num >= 0:
        interaction['prompt_number'] = num
    return interaction

def interact(opts, coqtop, src, start, end):
    input = src[start:end+1]
    # feed line to coqtop
    # remove any line breaks, we only want coqtop to prompt us once
    coqtop.stdin.write(bytes(input.replace('\n', ' ') + '\n', "utf-8"))
    coqtop.stdin.flush()
    # wait until prompt (re-)appears
    num, error = wait_for_prompt(opts, coqtop.stderr, opts.timeout)
    # read output produced so far
    # FIXME: this only works if all output fits into the OS's pipe buffer
    output = read_from_pipe(coqtop.stdout, 0)

    # extract any info messages from the output
    (infos, output) = extract_info_messages(output)

    interaction = {
        'start'    : start,
        'end'      : end,
        'input'    : input.rstrip().split('\n'),
    }

    if infos:
        interaction['messages'] = infos

    output = output.rstrip()
    if output:
        interaction['output'] = output.split('\n')

    error  = error.rstrip()
    if error:
        interaction['error'] = error

    if num >= 0:
        interaction['prompt_number'] = num

    return interaction

def report(n, interaction):
    print("+" * 80)
    if 'input' in interaction:
        print("INPUT < %d : [%s]" % (n, "\n".join(interaction['input'])))
    if 'output' in interaction:
        print("OUTPUT:\n%s" % "\n".join(interaction['output']))
    else:
        print("<NO-OUTPUT>")
    if 'error' in interaction:
        print("PROMPT: [%s]" % interaction['error'].strip())
    print("-" * 80)


def check_sync(opts, input_number, interaction):
    if 'prompt_number' in interaction:
        if interaction['prompt_number'] != input_number:
            print("Out of sync: prompt %d in response to input %d" %
                   (interaction['prompt_number'], input_number))
            if not opts.verbose:
                report(input_number, interaction)
            assert False # out of sync: we missed an answer somewhere

def feed_to_coqtop(opts, src):
    coqtop = launch_coqtop(opts)
    interactions = []

    # wait for coqtop startup to finish
    interaction = wait_for_coqtop(opts, coqtop)
    if opts.verbose:
        report(0, interaction)
    interactions.append(interaction)

    # feed statements
    last = 0
    for end in statement_end_offsets(opts, src):
        if opts.pause:
            time.sleep(0.1)
        interaction = interact(opts, coqtop, src, last, end)
        interactions.append(interaction)
        last = end + 1
        check_sync(opts, len(interactions), interaction)
        if opts.verbose:
            report(len(interactions), interaction)

    # signal end of input
    coqtop.stdin.close()

    # wait for coqtop to terminate
    trailing_interactions = 0
    while coqtop.poll() is None:
        interaction = wait_for_coqtop(opts, coqtop)
        if 'output' in interaction or 'error' in interaction:
            trailing_interactions += 1
            interactions.append(interaction)
            if opts.verbose:
                report(len(interactions), interaction)

    assert trailing_interactions <= 1

    return interactions

def process(opts, fname):
    print("Collecting proof state for %s..." % fname)
    src = open(fname, 'r').read()
    interactions = feed_to_coqtop(opts, src)
    ext = '.proofstate.yaml' if opts.yaml else '.proofstate.json'
    output_file = os.path.join(opts.output_prefix,
                               fname.replace('.v', ext))
    path = os.path.dirname(output_file)
    os.makedirs(path, exist_ok=True)
    out = open(output_file, 'w')
    if opts.yaml:
        yaml.dump(interactions, out, sort_keys=False)
    else:
        json.dump(interactions, out, sort_keys=False, indent=4)
    out.close()

def dump_structure(opts, fname):
    print("=" * 80)
    print("Statements in %s: \n" % fname)
    print("-" * 80)
    src = open(fname, 'r').read()
    last = 0
    for end in statement_end_offsets(opts, src):
        print("%s" % src[last:end+1].replace('\n', ' '))
        last = end + 1
        print("-" * 80)

def parse_args():
    parser = argparse.ArgumentParser(
        description="record proof state by interacting with coqtop")

    parser.add_argument('input_files', nargs='*',
        metavar='Coq-file',
        help='input Coq files (*.v)')

    parser.add_argument('-t', '--timeout', default=5,
                        action='store', type=float,
                        help='how long for coqtop to wait to respond (in seconds)')

    parser.add_argument('-c', '--coqtop-opts', default="",
                        action='store', type=str,
                        help='options to pass to coqtop')

    parser.add_argument('-o', '--output-prefix', default="./proof-state",
                        action='store', type=str,
                        help='path prefix for output file(s)')

    parser.add_argument('--yaml', default=False, action='store_true',
                        help='store results as YAML instead of JSON (requires pyyaml)')

    parser.add_argument('--verbose', default=False, action='store_true',
                        help='report on interaction with coqtop')

    parser.add_argument('--pause', default=False, action='store_true',
                        help='pause briefly before feeding data to coqtop')

    parser.add_argument('--parse-only', default=False, action='store_true',
                        help='report how the script splits the input '
                             '(--verbose for per-character info)')

    return parser.parse_args()

def main():
    opts = parse_args()

    # YAML is not part of the Python standard library, so complain if we don't
    # have it.
    if opts.yaml and not have_yaml:
        print("Error: could not import pyyaml library.", file=sys.stderr)
        sys.exit(2)

    had_problem = False
    for f in opts.input_files:
        try:
            if opts.parse_only:
                dump_structure(opts, f)
            else:
                process(opts, f)
        except OSError as e:
            print(e, file=sys.stderr)
            had_problem = True

    if had_problem:
        # signal something went wrong with non-zero exit code
        sys.exit(1)


if __name__ == '__main__':
    main()

