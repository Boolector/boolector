#!/usr/bin/env python3

import argparse
import subprocess
import os
import sys
from multiprocessing import Pool

g_args = None

ERR_KEYWORDS = ['Boolector under test changed',
                'not hashed',
                'but got',
                'ERROR: AddressSanitizer: heap-use-after-free',
                'ERROR: LeakSanitizer: detected memory leaks']

def get_num_lines(file):
    return sum(1 for line in open(file))

def progress(i):
    x = i % 4
    if x == 0:
        return '-'
    elif x == 1:
        return '\\'
    elif x == 2:
        return '|'
    return '/'

def untrace(trace):
    global g_args

    try:
        cmd = [g_args.untracer, trace]

        proc = subprocess.Popen(cmd,
                                stdin=subprocess.PIPE,
                                stdout=subprocess.PIPE,
                                stderr=subprocess.PIPE)
        _, err = proc.communicate(timeout=g_args.timeout)

        err = err.decode()

        if 'BTORLEAK' in err:
            return None

        for kw in ERR_KEYWORDS:
            if kw in err:
                err = kw
                break

        #if 'Non-destructive substitution' in err:
        #    os.remove(trace)
        #    return None

        new_err = [e for e in err.split('\n') if 'WARNING' not in e]
        err = '\n'.join(new_err).strip()

        if err:
            num_lines = get_num_lines(trace)
            return (err, num_lines, trace)
        return None
    except KeyboardInterrupt:
        return None
    except subprocess.TimeoutExpired:
        proc.terminate()
        if g_args.skip_timeout:
            return None
        return ('timeout', get_num_lines(trace), trace)

def reduce(info):
    err = info[0]
    trace = info[1]
    script_dir = os.path.dirname(os.path.abspath(__file__))
    ddmbt_path = os.path.join(script_dir, 'ddmbt.py')
    try:
        split_path = os.path.split(trace)
        red_trace = \
            os.path.join(split_path[0], 'red-{}'.format(split_path[1]))
        cmd = [ddmbt_path, '-vv', trace, red_trace, g_args.untracer]

        proc = subprocess.Popen(cmd,
                                stdin=subprocess.PIPE,
                                stdout=subprocess.PIPE,
                                stderr=subprocess.PIPE)
        _, _ = proc.communicate()

        return (err, get_num_lines(red_trace), red_trace)
    except KeyboardInterrupt:
        proc.terminate()
        return None


def main():
    global g_args

    ap = argparse.ArgumentParser()
    ap.add_argument('dir', nargs='+')
    ap.add_argument('-u', '--untracer', default='build/bin/btoruntrace',
                    help='Path to untracer')
    ap.add_argument('-r', '--reduce', default=False, action='store_true',
                    help='Reduce smallest trace for each group')
    ap.add_argument('-s', '--skip-timeout', default=False, action='store_true',
                    help='Ignore timeouts')
    ap.add_argument('-t', '--timeout', default=2, type=int,
                    help='btoruntrace timeout')
    ap.add_argument('-p', '--procs', default=1, type=int,
                    help='Number of parallel processes')

    g_args = ap.parse_args()

    errors = dict()
    traces = []
    for dir in g_args.dir:
        for root, dirs, files in os.walk(dir):
            for file in files:
                if file.endswith('.trace'):
                    traces.append(os.path.join(root, file))

    try:
        with Pool(processes=g_args.procs) as pool:
            for i, t in enumerate(pool.imap_unordered(untrace, traces, 1)):
                print('{} Checking {}/{}\r'.format(
                    progress(i), i, len(traces)),
                    file=sys.stderr, end='')
                if t:
                    err, num_lines, trace = t
                    files = errors.setdefault(err, [])
                    files.append((num_lines, trace))

    except KeyboardInterrupt:
        pass

    sorted_errors = sorted(errors.items(), key=lambda x: len(x[1]), reverse=True)

    if g_args.reduce:
        to_reduce = []
        for msg, traces in sorted_errors:
            traces = sorted(traces)
            trace = traces[0][1]
            to_reduce.append((msg, trace))

        try:
            with Pool(processes=g_args.procs) as pool:
                for i, t in enumerate(pool.imap_unordered(reduce, to_reduce, 1)):
                    print('{} Reducing {}/{}\r'.format(
                        progress(i), i, len(to_reduce)),
                        file=sys.stderr, end='')
                    if t:
                        err, num_lines, trace = t
                        files = errors.setdefault(err, [])
                        files.append((num_lines, trace))
        except KeyboardInterrupt:
            pool.terminate()
            pool.join()

        sorted_errors = sorted(errors.items(), key=lambda x: len(x[1]), reverse=True)


    for msg, traces in sorted_errors:
        print('{} {}'.format(len(traces), msg))
        traces_display = sorted(traces)[:5]
        print('\n{}\n'.format(
            '\n'.join('{} {}'.format(x, y) for x, y in traces_display)))


if __name__ == '__main__':
    main()
