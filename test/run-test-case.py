#!/usr/bin/env python3

import argparse
import os
import subprocess
import sys

def check(expected, out, err):
    out = out.decode()
    err = err.decode()
    if err:
        try:
            pos = err.index('log/')
            err = err[pos:]
        except ValueError:
            pass
    cmp = '{}{}'.format(out, err)
    if expected.strip() != cmp.strip():
        print("Expected:\n{}".format(expected.encode()), file=sys.stderr)
        print('=' * 80, file=sys.stderr)
        print("Got:\n{}".format(cmp.encode()), file=sys.stderr)
        sys.exit(1)


def main():
    print(sys.argv)
    ap = argparse.ArgumentParser()
    ap.add_argument('binary')
    ap.add_argument('testcase')
    ap.add_argument('--check-sat', action='store_true', default=False)
    ap.add_argument('--check-unsat', action='store_true', default=False)
    ap.add_argument('--check-output', action='store_true', default=False)
    args = ap.parse_args()

    btor_args = args.testcase.split()
    cmd_args = [args.binary]
    cmd_args.extend(btor_args)

    testname, _ = os.path.splitext(btor_args[0])
    outfilename = '{}.out'.format(testname)
    print(outfilename)
    print(btor_args)

    print("Running test case '{}'".format(' '.join(cmd_args)))

    proc = subprocess.Popen(cmd_args,
                            stdin=subprocess.PIPE,
                            stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE)

    out, err = proc.communicate()

    expected = None
    if args.check_sat:
        expected = 'sat'
    elif args.check_unsat:
        expected = 'unsat'
    else:
        assert args.check_output
        with open(outfilename, 'r') as outfile:
            expected = outfile.read()
    check(expected, out, err)


if __name__ == '__main__':
    main()
