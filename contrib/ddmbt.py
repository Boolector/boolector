#!/usr/bin/env python3

import copy
import os
import shlex
import shutil
import sys
from optparse import OptionParser
from subprocess import Popen, PIPE

g_golden_err_msg = ""
g_golden_exit_code = 0
g_options = object
g_outfile = ""
g_tmpfile = "/tmp/ddmbt-" + str(os.getpid()) + ".trace"
g_command = [] 
g_num_tests = 0
g_lines = []


def _parse_options():
    usage_fmt = "%prog [options] INFILE OUTFILE \"CMD [options]\""

    p = OptionParser(usage=usage_fmt)

    p.add_option("-v", action="count", dest="verbosity", default=0, 
                 help="increase verbosity level")

    # TODO: golden exit code
    (options, args) = p.parse_args()

    if len(args) != 3:
        p.error("invalid number of arguments")

    return (options, args)


def _parse_trace(inputfile):
    global g_lines

    try:
        with open(inputfile, 'r') as infile:
            for line in infile:
                g_lines.append(line)

        _log(1, "parsed {0:d} lines".format(len(g_lines)))

    except IOError as err:
        _error_and_exit(err)

def _open_file_dump_trace(filename, lines):
    try:
        with open(filename, 'w') as outfile:
            _dump_trace(outfile, lines)
    except IOError as err:
        _error_and_exit(err)

def _dump_trace(outfile, lines):

    for line in lines:
        outfile.write(line)

def _run():
    global g_command
    try:
        subproc = Popen(g_command, stdout=PIPE, stderr=PIPE)
#        subproc.wait()
        msg_out, msg_err = subproc.communicate()
        return (subproc.returncode, msg_err) 
    except OSError as err:
        _error_and_exit(err)

def _test():
    global g_golden_exit_code, g_num_tests, g_golden_err_msg

    g_num_tests += 1
    exitcode, err_msg = _run()
    return exitcode == g_golden_exit_code and err_msg == g_golden_err_msg

def _save(lines):
    global g_outfile

    _open_file_dump_trace(g_outfile, lines)

def _cleanup():
    os.remove(g_tmpfile)

def _log(verbosity, msg, update=False):
    global g_options

    if g_options.verbosity >= verbosity:
        sys.stdout.write(" " * 80 + "\r")
        if update:
            sys.stdout.write("[ddmbt] {0:s}\r".format(msg))
            sys.stdout.flush()
        else:
            sys.stdout.write("[ddmbt] {0:s}\n".format(msg))

def _error_and_exit(msg):
    sys.exit("[ddmbt] error: " + msg)

def _remove_lines():
    global g_lines

    gran = len(g_lines)

    num_lines = 0
    while gran >= 1:
        cur_lines = g_lines[:]
        last_saved_lines = g_lines[:]
        offset = 0
        while offset < len(cur_lines):
            lower = offset
            upper = offset + gran
            subset = cur_lines[lower:upper]
            lines = cur_lines[:lower]
            lines.extend(cur_lines[upper:])
            assert(len(subset) == len(cur_lines) - len(lines))
            assert(len(subset) > 0)
            assert(len(lines) < len(cur_lines))

            _open_file_dump_trace(g_tmpfile, lines)

            if _test():
                _save(lines)
                cur_lines = lines
                last_saved_lines = cur_lines[:]
                num_lines += len(subset)
            else:
                offset += gran

            _log(1, "  granularity {}, offset {}, lines {}".format(gran,
                 offset, len(last_saved_lines)), True)

        g_lines = last_saved_lines 
        gran = gran // 2

    return num_lines 

def _remove_return_pairs():
    global g_lines

    num_lines = 0
    cur_lines = g_lines[:]
    last_saved_lines = g_lines[:]
    offset = 0
    while offset < len(cur_lines):
        line = cur_lines[offset]

        if "return" in line:
            assert(offset > 0)
            lower = offset - 1
            upper = offset + 1
            subset = cur_lines[lower:upper]
            assert (len(subset) == 2)
            lines = cur_lines[:lower]
            lines.extend(cur_lines[upper:])
            assert(len(subset) == len(cur_lines) - len(lines))
            assert(len(subset) > 0)
            assert(len(lines) < len(cur_lines))

            _open_file_dump_trace(g_tmpfile, lines)

            if _test():
                _save(lines)
                cur_lines = lines
                last_saved_lines = cur_lines[:]
                num_lines += len(subset)
            else:
                offset += 1 
        else:
             offset += 1

        _log(1, "  pairs: offset {}, lines {}".format(offset,
             len(last_saved_lines)), True)

    g_lines = last_saved_lines 

    return num_lines 


def ddmbt_main(): 
    global g_options, g_golden_exit_code, g_tmpfile, g_outfile, g_command
    global g_num_tests, g_nodes, g_golden_err_msg

    (g_options, args) = _parse_options()
    inputfile = args[0]
    g_outfile = args[1]
    g_command = shlex.split(args[2])

    if not os.path.exists(inputfile):
        _error_and_exit("'input file {0:s}' does not exist".format(inputfile))

    if os.path.exists(g_outfile):
        _error_and_exit("output file '{0:s}' exists".format(g_outfile))

    _log(1, "input file: '{0:s}'".format(inputfile))
    _log(1, "output file: '{0:s}'".format(g_outfile))

    _parse_trace(args[0])

    # copy inputfile to tmpfile
    shutil.copyfile(inputfile, g_tmpfile)
    g_command.append(g_tmpfile)

    g_golden_exit_code, g_golden_err_msg = _run()
    _log(1, "golden exit code: {0:d}".format(g_golden_exit_code))

    rounds = 0
    pairs = False
    while True:
        rounds += 1

        num_lines = _remove_lines()

        if pairs:
            num_lines += _remove_return_pairs()

        _log(1, "round {}, removed {} lines".format(rounds, num_lines))

        if num_lines == 0 and not pairs:
            _log(1, "remove return pairs")
            pairs = True
        elif num_lines == 0:
            break


    _log(1, "tests: {0:d}".format(g_num_tests))
    _log(1, "dumped {0:d} lines".format(len(g_lines)))

if __name__ == "__main__":
    try:
        ddmbt_main()
        _cleanup()
        sys.exit(0)
    except KeyboardInterrupt as err:
        _cleanup()
        sys.exit(err)
