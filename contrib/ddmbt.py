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
g_tmpbin = "/tmp/ddmbt-bin-" + str(os.getpid())
g_command = [] 
g_num_tests = 0
g_lines = []
g_subst_lines = {}
g_line_tokens = []
g_id2line = {}
g_node_map = {}
g_node_bw = {}
g_sort_map = {}

CONST_NODE_KINDS = ["const", "zero", "false", "ones", "true", "one",
                    "unsigned_int", "int"]

NODE_KINDS = ["copy", "const", "zero", "false", "ones", "true", "one",
              "unsigned_int", "int", "var", "array", "uf", "not", "neg",
              "redor", "redxor", "redand", "slice", "uext", "sext", "implies",
              "iff", "xor", "xnor", "and", "nand", "or", "nor", "eq", "ne",
              "add", "uaddo", "saddo", "mul", "umulo", "smulo", "ult", "slt",
              "ulte", "slte", "ugt", "sgt", "ugte", "sgte", "sll", "srl",
              "sra", "rol", "ror", "sub", "usubo", "ssubo", "udiv", "sdiv",
              "sdivo", "urem", "srem", "smod", "concat", "read", "write",
              "cond", "param", "fun", "apply", "inc", "dec"]

SORT_KINDS = ["bool_sort", "bitvec_sort", "fun_sort", "array_sort",
              "tuple_sort"]

def _parse_options():
    usage_fmt = "%prog [options] INFILE OUTFILE \"CMD [options]\""

    p = OptionParser(usage=usage_fmt)

    p.add_option("-v", action="count", dest="verbosity", default=0, 
                 help="increase verbosity level")

    (options, args) = p.parse_args()

    if len(args) != 3:
        p.error("invalid number of arguments")

    return (options, args)

def _is_node(id):
    global g_node_map
    return id in g_node_map

def _sort_bw(id):
    global g_sort_map

    t = g_sort_map[id][:]
    del[t[1]]
    sort = t[0]

    if sort == "bool_sort":
        return 1
    elif sort == "bitvec_sort":
        return int(t[1])
    elif sort == "fun_sort":
        return [_sort_bw(s) for s in t[1:]]
    elif sort == "tuple_sort":
        pass
    elif sort == "array_sort":
        pass
    return 0

def _tokens_children(tokens):
    return [c for c in tokens if _is_node(c)]

def _node_bw(tokens):
    global g_nodes_bw

    t = tokens[:]
    del[t[1]]
    tokens = t
    kind = tokens[0]
    bw = 0
    if kind in ["var", "param", "zero", "one", "ones"]:
        bw = int(tokens[1])
    elif kind in ["int", "unsigned_int"]:
        bw = int(tokens[2])
    elif kind == "array":
        bw = [int(tokens[1]), int(tokens[2])]
    elif kind == "slice":
        bw = int(tokens[2]) - int(tokens[3]) + 1
    elif kind in ["true", "false",
                  "redor", "redand", "redxor",
                  "implies", "iff",
                  "eq", "ne", "umulo", "smulo",
                  "ult", "slt", "ulte", "slte",
                  "ugt", "sgt", "ugte", "sgte",
                  "uaddo", "saddo", "usubo", "ssubo", "sdivo"]:
        bw = 1 
    elif kind == "uf":
        bw = _sort_bw(tokens[1])
    else:
        children = _tokens_children(tokens)
        cbw = [g_node_bw[c] for c in children]
        if kind == "cond":
            assert(cbw[1] == cbw[2])
            bw = cbw[1]
        elif kind == "read":
            assert(len(cbw[0]) == 2)
            bw = cbw[0][0]
            assert(not isinstance(bw, list))
        elif kind == "write":
            assert(len(cbw[0]) == 2)
            bw = cbw[0]
        elif kind in ["not", "inc", "dec"]:
            assert(len(cbw) == 1)
            bw = cbw[0]
        elif kind in ["sext", "uext"]:
            assert(len(cbw) == 1)
            bw = cbw[0] + int(tokens[2])
        elif kind == "fun":
            bw = cbw
        elif kind == "apply":
            bw = cbw[-1][-1]
            assert(not isinstance(bw, list))
        elif kind in ["rol", "ror", "neg", "sll", "srl", "sra"]:
            bw = cbw[0]
        elif kind == "concat":
            assert(len(cbw) == 2)
            bw = cbw[0] + cbw[1]
        elif kind == "const":
            bw = len(tokens[1])
        elif kind == "copy":
            bw = cbw[0]
        else:
            assert(len(cbw) == 2)
            assert(cbw[0] == cbw[1])
            bw = cbw[0]
            assert(not isinstance(bw, list))
    return bw

def _is_node_id(s):
    m = re.match('^e-?\d+', s)
    return m is not None

def _is_sort_id(s):
    m = re.match('^s\d+', s)
    return m is not None

def _build_graph():
    global g_lines, g_line_tokens, g_id2line, g_node_map, g_node_bw, g_sort_map

    g_line_tokens = [] 
    g_node_map = {}
    g_node_bw = {}
    g_sort_map = {}
    prev_tokens = []
    for i in range(len(g_lines)):
        tokens = g_lines[i].split()
        bw = []
        nid = "" 

        if tokens[0] == "return" and not "assignment" in prev_tokens[0]:
            id = tokens[1]
            if prev_tokens[0] in NODE_KINDS and _is_node_id(id):
                g_node_map[id] = prev_tokens 
                bw = _node_bw(prev_tokens)
                g_node_bw[id] = bw
                assert(i > 0)
                g_line_tokens[i - 1][0] = id
                g_line_tokens[i - 1][1] = bw
                g_id2line[id] = i - 1
            elif prev_tokens[0] in SORT_KINDS and _is_sort_id(id):
                g_sort_map[id] = prev_tokens

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
        # TODO: sort handling
        # skip sort lines for now
        skip = False
        m = re.search('_sort$', lines[i].split()[0])
        if m is not None:
            skip = True
        if not skip:
            m = re.match('^return s\d+', lines[i])
            if m is not None:
                skip = True

        if skip:
            skip = True

        if i in g_subst_lines and not skip:
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
    os.remove(g_tmpbin)

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
        id = g_line_tokens[i][0]
        tokens = g_line_tokens[i][2]
        kind = tokens[0]

        if kind in CONST_NODE_KINDS or \
           kind in ["var", "param", "uf", "fun"] or not _is_node(id):
            continue

        btor = tokens[1]
        bw = g_line_tokens[i][1]

        _log(1, "  insert var at line {}, {}".format(i, num_substs), True)
        g_subst_lines[i] = "var {} {} v{}".format(btor, bw, i) 
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
                        break
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
    # copy binary to tmpfile
    shutil.copyfile(g_command[0], g_tmpbin)
    # copy permissons of binary
    shutil.copymode(g_command[0], g_tmpbin)
    # replace binary with temporary one
    g_command[0] = g_tmpbin

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
        num_substs = 0
        num_swaps = 0
        if num_lines == 0:
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
