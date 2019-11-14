#!/usr/bin/env python3

import argparse
import subprocess
import os
import sys
from multiprocessing import Pool

g_args = None

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
        cmd = [g_args.untracer, '-s', trace]

        proc = subprocess.Popen(cmd,
                                stdin=subprocess.PIPE,
                                stdout=subprocess.PIPE,
                                stderr=subprocess.PIPE)
        _, err = proc.communicate(timeout=g_args.timeout)

        err = err.decode()

        if 'BTORLEAK' in err:
            return None

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
        return ('timeout', 0, trace)


def main():
    global g_args

    ap = argparse.ArgumentParser()
    ap.add_argument('dir', nargs='+')
    ap.add_argument('-u', '--untracer', default='bin/btoruntrace',
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

    errors = sorted(errors.items(), key=lambda x: len(x[1]), reverse=True)

    for msg, traces in errors:
        print('{} {}'.format(len(traces), msg))
        traces_display = sorted(traces)[:5]
        print('\n{}\n'.format(
            '\n'.join('{} {}'.format(x, y) for x, y in traces_display)))


    if g_args.reduce:
        print('Reducing smallest trace in each group')
        script_dir = os.path.dirname(os.path.abspath(__file__))
        ddmbt_path = os.path.join(script_dir, 'ddmbt.py')
        for msg, traces in errors:
            traces = sorted(traces)
            trace = traces[0][1]
            split_path = os.path.split(trace)
            red_trace = \
                os.path.join(split_path[0], 'red-{}'.format(split_path[1]))
            cmd = [ddmbt_path, '-vv', trace, red_trace, g_args.untracer]

            proc = subprocess.Popen(cmd)
            _, _ = proc.communicate()

            print('Reduced {} ({}) to {} ({})\n'.format(
                trace, get_num_lines(trace),
                red_trace, get_num_lines(red_trace)))



if __name__ == '__main__':
    main()
