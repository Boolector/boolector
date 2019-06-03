#!/usr/bin/env python2.7
import argparse
import multiprocessing
import subprocess
import sys
import time
import signal
import os

g_result = None

DEFAULT_OPTIONS = ['--no-exit-codes', '-uc', '-br', 'fun',
                   '--declsort-bv-width=16',
                   '--simp-norm-adds']

CONFIGS = [
  ['-SE', 'cadical', '--fun:preprop', '--prop:nprops=10000'],
  ['-SE', 'cms'],
  ['-SE', 'lingeling'],
  ['-E', 'sls'],
]

def die(msg):
    print('error: {}'.format(msg))
    sys.exit(1)

def log(msg):
    if args.verbose:
        print('[poolector] {}'.format(msg))

# Spawn solver instance
def worker(i, procs):
    cmd = [args.binary]
    cmd.extend(DEFAULT_OPTIONS)
    cmd.extend(CONFIGS[i])
    cmd.append(args.benchmark)

    result = 'unknown'
    try:
        log('{} start: {}'.format(i, ' '.join(cmd)))
        start = time.time()
        proc = subprocess.Popen(
                    cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        procs[i] = proc.pid

        stdout, stderr = proc.communicate()
        result = ''.join([stdout, stderr]).strip()

        # Remove from process list since process terminated
        procs[i] = 0

        log('{} done: {} ({}s)'.format(i, result, time.time() - start))
    except subprocess.CalledProcessError as error:
        log('{} error: {}'.format(i, error.output.strip()))
    except:
        pass

    if result in ['sat', 'unsat']:
        return result
    return 'unknown'

# Terminate pool processes
def terminate(result):
    global g_result
    if not g_result and result in ['sat', 'unsat']:
        g_result = result
        pool.terminate()

def parse_args():
    ncpus = multiprocessing.cpu_count()
    ap = argparse.ArgumentParser()
    ap.add_argument('-c', dest='ncpus', type=int, default=ncpus)
    ap.add_argument('-v', dest='verbose', action='store_true')
    ap.add_argument('-b', dest='binary', type=str, default='./boolector')
    ap.add_argument('benchmark')
    return ap.parse_args()

if __name__ == '__main__':
    args = parse_args()
    try:
        with multiprocessing.Manager() as manager:
            #ncpus = min(len(CONFIGS), args.ncpus)

            # TODO: for SMT-COMP only
            ncpus = len(CONFIGS)
            procs = manager.list([0 for i in range(ncpus)])

            log('starting {} solver instances.'.format(ncpus))
            pool = multiprocessing.Pool(ncpus)
            for i in range(ncpus):
                pool.apply_async(worker, args=(i, procs), callback=terminate)
            pool.close()
            pool.join()

            # Kill remaining spawned solver processes
            for i in range(len(procs)):
                pid = procs[i]
                if pid == 0:
                    continue
                try:
                    os.kill(pid, signal.SIGKILL)
                    log('killed {} ({})'.format(i, pid))
                except OSError:
                    log('could not kill: {}'.format(pid))
    except:
        pass

    if g_result:
        print(g_result)
    else:
        print('unknown')
