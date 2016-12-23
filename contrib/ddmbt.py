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
g_lines = []        # contains the current failing trace
g_subst_lines = {}  # maps line number in 'g_lines' to line substitution
g_line_tokens = []
g_id2line = {}
g_node_map = {}
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

class LineTokens: 
    def __init__(self, id, line):
        tokens = line.split()
        self.id = id
        self.kind = tokens[0] 
        if len(tokens) > 1:
            self.btor = tokens[1]
        else:
            self.btor = ""
        self.tokens = tokens

        if self.is_node_kind():
            self.bw = _node_bw(self.tokens)
            self.children = [c for c in tokens if _is_node(c)]
        else:
            self.bw = None 
            self.children = []

    def is_node_kind(self):
        return self.kind in NODE_KINDS

    def is_sort_kind(self):
        return self.kind in SORT_KINDS

    def __str__(self):
        return "{} {} {}".format(self.id, self.bw, self.children)


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
    elif sort in ["fun_sort", "array_sort"]:
        return [_sort_bw(s) for s in t[1:]]
    elif sort == "tuple_sort":
        pass
    elif sort == "array_sort":
        pass
    return 0

def _tokens_children(tokens):
    return [c for c in tokens if _is_node(c)]

def _node_bw(tokens):
    t = tokens[:]
    del[t[1]]
    tokens = t
    kind = tokens[0]
    bw = 0
    if kind in ["var", "param", "zero", "one", "ones", "uf", "array"]:
        bw = _sort_bw(tokens[1])
    elif kind in ["int", "unsigned_int"]:
        bw = _sort_bw(tokens[2])
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
    else:
        children = _tokens_children(tokens)
        cbw = [g_node_map[c].bw for c in children]
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
    global g_lines, g_line_tokens, g_id2line, g_node_map, g_sort_map

    g_line_tokens = [] 
    g_node_map = {}
    g_sort_map = {}
    prev_ltok = None
    for i in range(len(g_lines)):
        line = g_lines[i]
        cur_ltok = LineTokens(None, line)

        if cur_ltok.kind == "return" and not "assignment" in prev_ltok.kind:
            id = cur_ltok.tokens[1]
            if prev_ltok.is_node_kind():
                g_node_map[id] = prev_ltok
                assert(i > 0)
                assert(g_line_tokens[i - 1].id == None)
                g_line_tokens[i - 1].id = id
                g_id2line[id] = i - 1
            elif prev_ltok.is_sort_kind():
                g_sort_map[id] = prev_ltok.tokens

        prev_ltok = LineTokens(None, line) 
        g_line_tokens.append(prev_ltok)
    
    for id,node in g_node_map.items():
        assert(id != None)
        assert(node.id == id)

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
        id = g_line_tokens[i].id
        tokens = g_line_tokens[i].tokens
        kind = tokens[0]

        if kind in CONST_NODE_KINDS or \
           kind in ["var", "param", "uf", "fun"] or not _is_node(id):
            continue

        btor = tokens[1]
        bw = g_line_tokens[i].bw

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
    assert(nid in g_node_map)

    i = g_id2line[nid]
    bw = g_line_tokens[i].bw
    assert (bw != None)
    candidates = []
    cache = {}
    for j in range(i):
        ltok = g_line_tokens[j]
        if ltok.id != None and ltok.bw == bw and ltok.id not in cache and \
           ltok.id != nid:
            cache[ltok.id] = True
            candidates.append(ltok.id)

    return candidates


def _swap_ids():
    global g_line_tokens, g_subst_lines, g_lines

    num_substs = 0
    g_subst_lines = {}

    _build_graph()
    assert(len(g_lines) == len(g_line_tokens))

    for i in range(len(g_line_tokens)):
        ltok = g_line_tokens[i]

        if ltok.id is None:
            continue

        tokens = [str(t) for t in ltok.tokens]
        for child in ltok.children:
            assert(_is_node(child))
            if len(g_node_map[child].children) == 0:
                continue
            candidates = _swap_candidates(child)

            for c in candidates:
                assert(child != c)
                swapped = False
                pos = 0
                while pos < len(tokens):
                    if tokens[pos] == child:
                        tokens[pos] = c
                        swapped = True
                        break
                    pos += 1

                if not swapped:
                    continue

                g_subst_lines[i] = " ".join(tokens)
                assert(g_subst_lines[i] != g_lines[i])
                _log(1, "  line {}, swap nodes {}".format(i, num_substs), True)
                _open_file_dump_trace(g_tmpfile, g_lines)

                if _test():
                    _save(g_lines)
                    g_lines[i] = g_subst_lines[i]
                    num_substs += 1
                    break
                else:
                    tokens[pos] = child

                del(g_subst_lines[i])

    return num_substs


def _remove_return_pairs():
    global g_lines

    num_lines = 0
    cur_lines = g_lines[:]
    last_saved_lines = g_lines[:]
    offset = 0

    # remove get_width etc.
    num = 0
    prev_kind = None 
    while offset < len(cur_lines):
        line = cur_lines[offset]
        kind = line.split()[0]
        prev_kind = kind if prev_kind is None else prev_kind

        if "return" in kind and prev_kind != kind and \
            ("get_" in prev_kind or "is_" in prev_kind or \
            "_assignment" in prev_kind):
            cur_lines.pop(offset - 1)
            cur_lines.pop(offset - 1)
            num_lines += 2
            offset -= 1
        elif "free_" in kind and "assignment" in kind: 
            cur_lines.pop(offset)
            num_lines += 1
        else:
            offset += 1
        prev_kind = kind

    _open_file_dump_trace(g_tmpfile, cur_lines)

    if _test():
        _save(cur_lines)
        last_saved_lines = cur_lines[:]
    else:
        cur_lines = g_lines[:]
        last_saved_lines = g_lines[:]

    if num_lines == 0:
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
    _log(1, "golden err msg: {}".format(g_golden_err_msg))

    rounds = 0
    last_num_lines = last_num_substs = last_num_swaps = 0
    num_swap_only_rounds = 0
    while True:
        rounds += 1

        if last_num_lines > 0 or rounds % 5 == 1:
            num_lines = _remove_return_pairs()
            num_lines += _remove_lines()
            if num_lines > 0:
                num_swap_only_rounds = 0
        if last_num_substs > 0 or rounds % 5 == 1:
            num_substs = _compact_graph()
            if num_substs > 0:
                num_swap_only_rounds = 0
        if last_num_swaps > 0 or rounds % 5 == 1:
            num_swaps = _swap_ids()
            if num_lines == 0 and num_substs == 0:
                num_swap_only_rounds += 1


        _log(1, "round {}, removed {} lines, substituted {} lines, "\
                "swapped {} nodes".format(rounds, num_lines,
                                          num_substs, num_swaps))

        if (num_lines == 0 and num_substs == 0 and num_swaps == 0) or \
            num_swap_only_rounds >= 3:
            num_lines = _remove_return_pairs()
            num_lines += _remove_lines()

            if num_lines == 0:
                break

        last_num_lines = num_lines
        last_num_substs = num_substs
        last_num_swaps = num_swaps

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
