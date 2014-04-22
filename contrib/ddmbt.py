#!/usr/bin/env python3

import copy
import os
import shlex
import shutil
import sys
import re
import time
from optparse import OptionParser
from subprocess import Popen, PIPE, TimeoutExpired

g_golden_err_msg = ""
g_golden_exit_code = 0
g_golden_runtime = 0
g_options = object
g_outfile = ""
g_tmpfile = "/tmp/ddmbt-" + str(os.getpid()) + ".trace"
g_command = [] 
g_num_tests = 0
g_lines = []
g_subst_lines = {}
g_line_tokens = []
g_id2line = {}
g_ids = []

SKIP_SUBST_LIST = ["return", "release", "get_index_width", "bv_assignment", \
                   "free_bv_assignment", "get_width", "get_fun_arity"]

def _parse_options():
    usage_fmt = "%prog [options] INFILE OUTFILE \"CMD [options]\""

    p = OptionParser(usage=usage_fmt)

    p.add_option("-v", action="count", dest="verbosity", default=0, 
                 help="increase verbosity level")

    (options, args) = p.parse_args()

    if len(args) != 3:
        p.error("invalid number of arguments")

    return (options, args)

def _is_node(s):
    m = re.match('^e-?\d+', s)
    return m is not None

def _tokens_children(tokens):
    return [c for c in tokens if _is_node(c)]

def _tokens_bw(tokens, nodes_bw):

    kind = tokens[0]
    if kind in ["var", "param", "zero", "one", "ones"]:
        return [int(tokens[1])]
    elif kind in ["int", "unsigned_int"]:
        return [int(tokens[2])]
    elif kind == "array":
        return [int(tokens[1]), int(tokens[2])]
    elif kind == "slice":
        return [int(tokens[2]) - int(tokens[3]) + 1]
    elif kind in ["zero", "ones", "one"]:
        return [int(tokens[1])]
    elif kind in ["true", "false",
                  "redor", "redand", "redxor",
                  "implies", "iff",
                  "eq", "ne", "umulo", "smulo",
                  "ult", "slt", "ulte", "slte",
                  "ugt", "sgt", "ugte", "sgte",
                  "uaddo", "saddo", "usubo", "ssubo", "sdivo"]:
        return [1]
    else:
        children = _tokens_children(tokens)
        cbw = [nodes_bw[c] for c in children]
        if kind == "cond":
            assert(cbw[1] == cbw[2])
            return cbw[1]
        elif kind == "read":
            assert(len(cbw[0]) == 2)
            return [cbw[0][0]]
        elif kind == "write":
            assert(len(cbw[0]) == 2)
            return cbw[0]
        elif kind in ["not", "inc", "dec"]:
            assert(len(cbw) == 1)
            return cbw[0]
        elif kind in ["sext", "uext"]:
            assert(len(cbw) == 1)
            return [cbw[0][0] + int(tokens[2])]
        elif kind in ["fun", "apply"]:
            return cbw[-1]
        elif kind in ["rol", "ror", "neg", "sll", "srl", "sra"]:
            return cbw[0]
        elif kind == "concat":
            assert(len(cbw) == 2)
            return [cbw[0][0] + cbw[1][0]]
        elif kind == "const":
            return [len(tokens[1])]
        elif kind == "copy":
            return cbw[0]
        else:
            assert(len(cbw) == 2)
            assert(cbw[0] == cbw[1])
            return cbw[0]

def _build_graph():
    global g_lines, g_line_tokens, g_ids, g_id2line

    g_line_tokens = [] 
    node_map = {}
    nodes_bw = {}
    prev_tokens = []
    for i in range(len(g_lines)):
        tokens = g_lines[i].split()
        bw = []
        nid = "" 

        if tokens[0] == "return" and not "assignment" in prev_tokens[0]:
            if _is_node(tokens[1]):
                nid = tokens[1]
                g_ids.append(nid)
                node_map[nid] = prev_tokens 
                bw = _tokens_bw(prev_tokens, nodes_bw) 
                nodes_bw[nid] = bw
                assert(i > 0)
                g_line_tokens[i - 1][0] = nid
                g_line_tokens[i - 1][1] = bw
                g_id2line[nid] = i - 1

        prev_tokens = tokens
        g_line_tokens.append(["", [], tokens])

def _parse_trace(inputfile):
    global g_lines

    try:
        with open(inputfile, 'r') as infile:
            for line in infile:
                g_lines.append(line.strip())

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
    global g_subst_lines

    for i in range(len(lines)):
        if i in g_subst_lines:
            line = g_subst_lines[i]
        else:
            line = lines[i]

        outfile.write("{}\n".format(line))

def _run(initial=False):
    global g_command
    try:
        subproc = Popen(g_command, stdout=PIPE, stderr=PIPE)
        try:
            if initial:
              msg_out, msg_err = subproc.communicate()
            else:
                timeout = max([g_golden_runtime * 2, 1])
                msg_out, msg_err = subproc.communicate(timeout=timeout)
        except TimeoutExpired:
            subproc.kill()
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

def _compact_graph():
    global g_line_tokens, g_subst_lines, g_lines

    num_substs = 0
    g_subst_lines = {}

    _build_graph()
    assert(len(g_lines) == len(g_line_tokens))

    # insert vars
    for i in range(len(g_line_tokens)):
        nid = g_line_tokens[i][0]
        bw = g_line_tokens[i][1]
        tokens = g_line_tokens[i][2]
        kind = tokens[0]

        if kind in ["var", "fun", "param"] or nid == "" or len(bw) > 1:
            continue

        _log(1, "  insert var at line {}, {}".format(i, num_substs), True)
        g_subst_lines[i] = "var {} v{}".format(bw[0], i) 
        _open_file_dump_trace(g_tmpfile, g_lines)

        if _test():
            _save(g_lines)
            g_lines[i] = g_subst_lines[i]
            num_substs += 1

        del(g_subst_lines[i])

    return num_substs

def _swap_candidates(nid):
    global g_line_tokens, g_id2line

    i = g_id2line[nid]
    bw = g_line_tokens[i][1]

    candidates = []
    for j in range(i):
        if g_line_tokens[j][1] == bw:
            candidates.append(g_line_tokens[j][0])

    return candidates


def _swap_ids():
    global g_line_tokens, g_subst_lines, g_lines

    num_substs = 0
    g_subst_lines = {}

    _build_graph()
    assert(len(g_lines) == len(g_line_tokens))

    for i in range(len(g_line_tokens)):
        nid = g_line_tokens[i][0]
        bw = g_line_tokens[i][1]
        tokens = g_line_tokens[i][2]
        kind = tokens[0]

        if nid == "":
            continue;

        for j in range(len(tokens)):
            if _is_node(tokens[j]):
                candidates = _swap_candidates(tokens[j])

                t = [str(tt) for tt in tokens]
                for c in candidates:
                    old = t[j]
                    t[j] = str(c)
                    g_subst_lines[i] = " ".join(t)
                    _log(1, "  line {}, swap nodes {}".format(i, num_substs),
                         True)
                    _open_file_dump_trace(g_tmpfile, g_lines)

                    if _test():
                        _save(g_lines)
                        g_lines[i] = g_subst_lines[i]
                        num_substs += 1
                    else:
                        t[j] = old

                    del(g_subst_lines[i])

    return num_substs


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
    num_lines_start = len(g_lines)

    # copy inputfile to tmpfile
    shutil.copyfile(inputfile, g_tmpfile)
    g_command.append(g_tmpfile)

    start = time.time()
    g_golden_exit_code, g_golden_err_msg = _run(True)
    g_golden_runtime = time.time() - start
    _log(1, "golden exit code: {0:d} in {1:.3f} seconds".format(
            g_golden_exit_code, g_golden_runtime))

    rounds = 0
    pairs = False
    while True:
        rounds += 1

        num_lines = _remove_lines()
        num_substs = _compact_graph()
        num_swaps = _swap_ids()

        if pairs:
            num_lines += _remove_return_pairs()

        _log(1, "round {}, removed {} lines, substituted {} lines, swapped {} nodes".format(
             rounds, num_lines, num_substs, num_swaps))

        if num_lines == 0 and not pairs:
            _log(1, "remove return pairs")
            pairs = True
        elif num_lines == 0 and num_substs == 0 and num_swaps == 0:
            break


    _log(1, "tests: {0:d}".format(g_num_tests))
    _log(1, "dumped {0:d} lines (removed {1:.1f}% of lines)".format(
         len(g_lines), (1 - len(g_lines)/num_lines_start) * 100))

if __name__ == "__main__":
    try:
        ddmbt_main()
        _cleanup()
        sys.exit(0)
    except KeyboardInterrupt as err:
        _cleanup()
        sys.exit(err)
