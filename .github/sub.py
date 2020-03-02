#!/usr/bin/env python3
import sys

with open(sys.argv[1]) as fd:
    backtrace = fd.read()
with open(sys.argv[2]) as fd:
    source = fd.read()

for line in sys.stdin:
    print(line, end='')
    if "RUST_BACKTRACE=1" in line:
        line = input()
        while line == "":
            print()
            line = input()
        print(line)
        if "```" not in line:
            continue
        print(backtrace, end='')
    # source code for file
    elif '```c' in line:
        print(source, end='')
