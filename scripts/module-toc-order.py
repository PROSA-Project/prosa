#!/usr/bin/env python3

import os
import sys

MODULE_ORDER = [
    'behavior.time',
    'behavior.job',
    'behavior.schedule',
    'behavior.service',
    'behavior.arrival_sequence',
    'behavior.ready',
    'behavior',
    'model.processor',
    'model.readiness',
    'model.preemption',
    'model.task',
    'model.priority',
    'model.schedule',
    'model',
    'results',
    'analysis',
    'classic',
    'util',
]

def modorder(fname):
    modname = fname.replace('./', '').replace('.v', '').replace('/', '.')
    for i, prefix in enumerate(MODULE_ORDER):
        if modname.startswith(prefix):
            return (i, modname)
    return (len(MODULE_ORDER), modname)

def main():
    lines = sys.stdin.readlines()
    for l in sorted(lines, key=modorder):
        print(l, end='')

if __name__ == '__main__':
    main()

