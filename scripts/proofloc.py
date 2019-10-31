#!/usr/bin/env python3

import argparse
import re
import json
import sys

from collections import defaultdict

SINGLE_LINE_PROOF_PATTERN = re.compile(
r"""
([ \t]|^)Proof\.  # Proof keyword
.*             # The actual proof.
[ \t.]Qed\.   # End of proof keyword.
"""
, re.VERBOSE)

PROOF_START_PATTERN = re.compile(r"[ \t^](Proof|Next +Obligation)\.")
PROOF_END_PATTERN = re.compile(r"[ \t^.](Qed|Defined)\.")

CLAIM_NAME_PATTERN = re.compile(
r"""
# first a keyword indicating a claim
(Lemma|Theorem|Corollary|Fact|Remark|Example)
\s+       # whitespace
([^:\s]+) # the identifier (anything up to the first space or colon)
"""
, re.VERBOSE)

COMMENT_START_PATTERN = re.compile(r"\(\*")
COMMENT_END_PATTERN = re.compile(r"\*\)")

def banner(fname):
    fill1 = (76 - len(fname)) // 2
    fill2 = 76 - len(fname) - fill1
    print("%s[ %s ]%s" % ('=' * fill1, fname, '=' * fill2))

def show_line(tag, line_number, line):
    print("%3s %4d %s" % (tag, line_number + 1, line), end='')

def silent(tag, line_number, line):
    pass

def process_file(fname, annotate=silent):
    proofs = []
    in_proof = False
    in_comment = 0
    claim = '???'
    with open(fname) as f:
        for i, line in enumerate(f):
            # simplification: we assume comment start/end not on otherwise
            # significant lines
            in_comment += len(COMMENT_START_PATTERN.findall(line))
            in_comment -= len(COMMENT_END_PATTERN.findall(line))
            assert in_comment >= 0
            name_match = CLAIM_NAME_PATTERN.search(line)
            if not name_match is None:
                claim = name_match.group(2)
            if in_proof:
                if not in_comment and PROOF_END_PATTERN.search(line):
                    annotate('###', i, line)
                    proofs.append( (fname, start + 1, claim, i - start - 1) )
                    in_proof = False
                    claim = '???'
                else:
                    annotate(' P ', i, line)
            elif not in_comment and SINGLE_LINE_PROOF_PATTERN.search(line):
                annotate('*P*', i, line)
                proofs.append( (fname, i + 1, claim, 1) )
                claim = '???'
            elif not in_comment and PROOF_START_PATTERN.search(line):
                annotate('***', i, line)
                in_proof = True
                start = i
            else:
                annotate('   ', i, line)

    return proofs

def show_histogram(opts, all_proofs):
    limit = 0
    counts = []
    for fname, line, claim, length in reversed(all_proofs):
        if length > limit:
            limit += opts.bin_size
            counts.append(0)
        counts[-1] += 1
    print("     LOC  #Proofs")
    print("=" * 19)
    for i, count in enumerate(counts):
        print("  <= %3d  %7d" % ((i + 1) * opts.bin_size, count))

def create_db(opts, all_proofs):
    db = {}
    db["manual_exceptions"] = opts.long_proofs["manual_exceptions"]
    db["legacy_proofs"] = defaultdict(dict)
    for fname, line, claim, length in all_proofs:
        if fname in db["manual_exceptions"] and \
            claim in db["manual_exceptions"][fname]:
                # skip manually approved long proofs
                continue
        if length >= opts.threshold:
            db["legacy_proofs"][fname][claim] = length
    print(json.dumps(db, sort_keys=True, indent=4))

def check_proof_lengths(opts, all_proofs):
    new_long_proofs = False
    known_long_proofs = 0
    for fname, line, claim, length in all_proofs:
        if length <= opts.threshold:
            break
        known = False
        for category in ["manual_exceptions", "legacy_proofs"]:
            if fname in opts.long_proofs[category] and \
                claim in opts.long_proofs[category][fname] and \
                    opts.long_proofs[category][fname][claim] >= length:
                        # this is a known long proof of non-increased length
                        # no need to complain
                        known = True
        if not known:
            print("Warning: new long proof of %s in %s:%d!"
                    % (claim, fname, line), file=sys.stderr)
            new_long_proofs = True
        else:
            known_long_proofs = known_long_proofs + 1
    print("Checked %d proofs in %d files, while skipping %d known long proofs."
            % (len(all_proofs), len(opts.input_files), known_long_proofs))
    return new_long_proofs

def rank_proofs(opts, all_proofs):
    print("%12s   %s" % ("Proof LOC", "Location (Claim)"))
    print("=" * 80)
    for fname, line, claim, length in all_proofs:
        if (not opts.extract) and length <= opts.threshold:
            break
        print("%12d   %s:%d (%s)" % (length, fname, line, claim))

def parse_args():
    parser = argparse.ArgumentParser(
        description="Proof counting tool")

    parser.add_argument('input_files', nargs='*',
        metavar='Coq-file',
        help='input Coq files (*.v)')

    parser.add_argument('-t', '--threshold', default=40,
                        action='store', type=int,
                        help='up to which length is a proof is considered ok')

    parser.add_argument('-b', '--bin-size', default=None,
                        action='store', type=int, metavar="BIN-SIZE",
                        help='report length histogram with given bin size')

    parser.add_argument('--extract', default=False, action='store_true',
                        help='simply list all identified proofs')

    parser.add_argument('--annotate', default=False, action='store_true',
                        help='dump the file with proofs marked')

    parser.add_argument('--create-db', default=False, action='store_true',
                        help='create a DB of known long proofs (JSON format)')

    parser.add_argument('--long-proofs', default=None,
                        type=argparse.FileType('r'), metavar="JSON-FILE",
                        help='JSON DB of known long proofs')

    parser.add_argument('--check', default=False, action='store_true',
                        help='complain and return non-zero exit code if there '
                             'are new too-long proofs')

    return parser.parse_args()

def main():
    opts = parse_args()

    if opts.long_proofs:
        opts.long_proofs = json.load(opts.long_proofs)
    else:
        opts.long_proofs = { "manual_exceptions" : {}, "legacy_proofs" : {} }

    all_proofs = []
    annotate = show_line if opts.annotate else silent
    for f in opts.input_files:
        if opts.annotate:
            banner(f)
        all_proofs += process_file(f, annotate=annotate)
        if opts.annotate:
            print("\n")

    if not opts.extract:
        all_proofs.sort(key=lambda x: x[3], reverse=True)

    if opts.bin_size:
        show_histogram(opts, all_proofs)
    elif opts.create_db:
        create_db(opts, all_proofs)
    elif opts.check:
        sys.exit(check_proof_lengths(opts, all_proofs))
    else:
        rank_proofs(opts, all_proofs)

if __name__ == '__main__':
    main()

