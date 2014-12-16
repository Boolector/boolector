#! /usr/bin/env python3

import boolector
import sys
import random
import re
from optparse import OptionParser

g_btor = None
g_options = None
g_nodemap = {}
g_symbolmap = {}
g_model_vars = {}
g_model_arrays = {}

def error_and_exit(msg):
    sys.exit("[btorcheckmodel] error: " + msg)


def log(verbosity, msg, update=False):
    global g_options

    if g_options.verbosity >= verbosity:
        sys.stdout.write(" " * 80 + "\r")
        if update:
            sys.stdout.write("[btorcheckmodel] {0:s}\r".format(msg))
            sys.stdout.flush()
        else:
            sys.stdout.write("[btorcheckmodel] {0:s}\n".format(msg))


def parse_options():
    usage_fmt = "%prog [options] <BTOR formula> <BTOR model>"

    p = OptionParser(usage=usage_fmt)

    p.add_option("-v", action="count", dest="verbosity", default=0, 
                 help="increase verbosity level")

    (options, args) = p.parse_args()

    if len(args) != 2:
        p.error("invalid number of arguments")

    return (options, args)


def get_children(tokens, offset, length = 0):
    global g_btor, g_nodemap

    if length == 0:
        length = len(tokens)

    c = []
    for id in [int(i) for i in tokens[offset:length]]:
        if id < 0:
            n = g_btor.Not(g_nodemap[-id])
        else:
            n = g_nodemap[id]
        c.append(n)

    return c


def add_node(tokens):
    global g_btor, g_nodemap, g_symbolmap

    id = int(tokens[0])
    kind = tokens[1]
    width = int(tokens[2])

    n = None
    if kind == "add":
        c = get_children(tokens, 3)
        n = g_btor.Add(c[0], c[1])
    elif kind == "and":
        c = get_children(tokens, 3)
        n = g_btor.And(c[0], c[1])
    elif kind == "apply":
        c = get_children(tokens, 3)
        assert(len(c) == 2)
#        if c[0].is_array():
#            print(c[1])
#            n = g_btor.Read(c[0], c[1][0])
#        else:
        if c[0].is_array_var():
            assert(len(c[1]) == 1)
            n = g_btor.Read(c[0], c[1][0])
        else:
            n = g_btor.Apply(c[1], c[0])
    elif kind == "args":
        c = get_children(tokens, 3)
        n = []
        for cc in c:
            if isinstance(cc, list):
                n.extend(cc)
            else:
                n.append(cc)
    # represent array model as chain of writes
    elif kind == "array":
        m = None
        key = None
        i_width = int(tokens[3])
        if len(tokens) == 5:
            sym = tokens[4]
            n = g_btor.Array(width, i_width, sym)
            assert(sym not in g_symbolmap)
            g_symbolmap[sym] = n

            key = sym
        else:
            n = g_btor.Array(width, i_width)
            key = str(id)

        if key in g_model_arrays:
            m = g_model_arrays[key]
            a = n
            for i, v in m.items():
                c_i = g_btor.Const(i)
                c_v = g_btor.Const(v)
                a = g_btor.Write(a, c_i, c_v)

            n = a
    elif kind == "concat":
        c = get_children(tokens, 3)
        n = g_btor.Concat(c[0], c[1])
    elif kind == "cond" or kind == "acond":
        c = get_children(tokens, 3)
        n = g_btor.Cond(c[0], c[1], c[2])
    elif kind == "const":
        n = g_btor.Const(tokens[3])
    elif kind == "constd" or kind == "consth":
        bits = "{0:b}".format(tokens[4])
        if len(bits) < width:
            bits = "0" * (width - len(bits)) + bits
        assert(len(bits) == width)
        n = g_btor.Const(bits)
    elif kind == "eq":
        c = get_children(tokens, 3)
        n = g_btor.Eq(c[0], c[1])
    elif kind == "iff":
        c = get_children(tokens, 3)
        n = g_btor.Iff(c[0], c[1])
    elif kind == "implies":
        c = get_children(tokens, 3)
        n = g_btor.Implies(c[0], c[1])
    elif kind == "lambda":
        c = get_children(tokens, 4)
        n = g_btor.Fun([c[0]], c[1])
    elif kind == "mul":
        c = get_children(tokens, 3)
        n = g_btor.Mul(c[0], c[1])
    elif kind == "nand":
        c = get_children(tokens, 3)
        n = g_btor.Nand(c[0], c[1])
    elif kind == "neg":
        c = get_children(tokens, 3)
        n = g_btor.Neg(c[0])
    elif kind == "inc":
        c = get_children(tokens, 3)
        n = g_btor.Inc(c[0])
    elif kind == "dec":
        c = get_children(tokens, 3)
        n = g_btor.Dec(c[0])
    elif kind == "ne":
        c = get_children(tokens, 3)
        n = g_btor.Ne(c[0], c[1])
    elif kind == "nor":
        c = get_children(tokens, 3)
        n = g_btor.Nor(c[0], c[1])
    elif kind == "not":
        c = get_children(tokens, 3)
        n = g_btor.Not(c[0], c[1])
    elif kind == "one":
        n = g_btor.One(width)
    elif kind == "ones":
        n = g_btor.Ones(width)
    elif kind == "or":
        c = get_children(tokens, 3)
        n = g_btor.Or(c[0], c[1])
    elif kind == "param":
        if len(tokens) == 4:
            n = g_btor.Param(width, tokens[3])
        else:
            n = g_btor.Param(width)
    elif kind == "read":
        c = get_children(tokens, 3)
        n = g_btor.Read(c[0], c[1])
    elif kind == "redand":
        c = get_children(tokens, 3)
        n = g_btor.Redand(c[0])
    elif kind == "redor":
        c = get_children(tokens, 3)
        n = g_btor.Redor(c[0])
    elif kind == "redxor":
        c = get_children(tokens, 3)
        n = g_btor.Redxor(c[0])
    elif kind == "rol":
        c = get_children(tokens, 3)
        n = g_btor.Rol(c[0], c[1])
    elif kind == "root":
        c = get_children(tokens, 3)
        g_btor.Assert(c[0])
    elif kind == "ror":
        c = get_children(tokens, 3)
        n = g_btor.Ror(c[0], c[1])
    elif kind == "saddo":
        c = get_children(tokens, 3)
        n = g_btor.Saddo(c[0], c[1])
    elif kind == "sdivo":
        c = get_children(tokens, 3)
        n = g_btor.Sdivo(c[0], c[1])
    elif kind == "sdiv":
        c = get_children(tokens, 3)
        n = g_btor.Sdiv(c[0], c[1])
    elif kind == "sext":
        c = get_children(tokens, 3, 4)
        n = g_btor.Sdiv(c[0], int(tokens[4]))
    elif kind == "sgte":
        c = get_children(tokens, 3)
        n = g_btor.Sgte(c[0], c[1])
    elif kind == "sgt":
        c = get_children(tokens, 3)
        n = g_btor.Sgt(c[0], c[1])
    elif kind == "slice":
        c = get_children(tokens, 3, 4)
        upper = int(tokens[4])
        lower = int(tokens[5])
        n = g_btor.Slice(c[0], upper, lower)
    elif kind == "sll":
        c = get_children(tokens, 3)
        n = g_btor.Sll(c[0], c[1])
    elif kind == "slte":
        c = get_children(tokens, 3)
        n = g_btor.Slte(c[0], c[1])
    elif kind == "slt":
        c = get_children(tokens, 3)
        n = g_btor.Slt(c[0], c[1])
    elif kind == "smod":
        c = get_children(tokens, 3)
        n = g_btor.Smod(c[0], c[1])
    elif kind == "smulo":
        c = get_children(tokens, 3)
        n = g_btor.Smulo(c[0], c[1])
    elif kind == "sra":
        c = get_children(tokens, 3)
        n = g_btor.Sra(c[0], c[1])
    elif kind == "srem":
        c = get_children(tokens, 3)
        n = g_btor.Srem(c[0], c[1])
    elif kind == "srl":
        c = get_children(tokens, 3)
        n = g_btor.Srl(c[0], c[1])
    elif kind == "ssubo":
        c = get_children(tokens, 3)
        n = g_btor.Ssubo(c[0], c[1])
    elif kind == "sub":
        c = get_children(tokens, 3)
        n = g_btor.Sub(c[0], c[1])
    elif kind == "uaddo":
        c = get_children(tokens, 3)
        n = g_btor.Uaddo(c[0], c[1])
    elif kind == "udiv":
        c = get_children(tokens, 3)
        n = g_btor.Udiv(c[0], c[1])
    elif kind == "uext":
        c = get_children(tokens, 3, 4)
        n = g_btor.Uaddo(c[0], int(tokens[4]))
    elif kind == "ugte":
        c = get_children(tokens, 3)
        n = g_btor.Ugte(c[0], c[1])
    elif kind == "ugt":
        c = get_children(tokens, 3)
        n = g_btor.Ugt(c[0], c[1])
    elif kind == "ulte":
        c = get_children(tokens, 3)
        n = g_btor.Ulte(c[0], c[1])
    elif kind == "ult":
        c = get_children(tokens, 3)
        n = g_btor.Ult(c[0], c[1])
    elif kind == "umulo":
        c = get_children(tokens, 3)
        n = g_btor.Umulo(c[0], c[1])
    elif kind == "urem":
        c = get_children(tokens, 3)
        n = g_btor.Urem(c[0], c[1])
    elif kind == "usubo":
        c = get_children(tokens, 3)
        n = g_btor.Usubo(c[0], c[1])
    # substitute var with constant from model
    elif kind == "var":
        if len(tokens) == 4:
            sym = tokens[3]
            assert(sym not in g_symbolmap)
            g_symbolmap[sym] = n
            bits = g_model_vars[sym]
        else:
            bits = g_model_vars[str(id)]

        assert(len(bits) == width)
        n = g_btor.Const(bits)
#    elif kind == "var":
#        if len(tokens) == 4:
#            sym = tokens[3]
#            n = g_btor.Var(width, sym)
#            assert(sym not in g_symbolmap)
#            g_symbolmap[sym] = n
#        else:
#            n = g_btor.Var(width)
    elif kind == "write":
        c = get_children(tokens, 4)
        n = g_btor.Write(c[0], c[1], c[2])
    elif kind == "xnor":
        c = get_children(tokens, 3)
        n = g_btor.Xnor(c[0], c[1])
    elif kind == "xor":
        c = get_children(tokens, 3)
        n = g_btor.Xor(c[0], c[1])
    elif kind == "zero":
        n = g_btor.Zero(width)
    else:
        error_and_exit("invalid node kind: {}".format(kind))

    if n is not None:
        assert(id not in g_nodemap)
        g_nodemap[id] = n


def parse_btor(inputfile):
    global g_btor

    try:
        with open(inputfile, 'r') as infile:
            for line in infile:
                t = line.split()

                if len(t) == 0 or t[0][0] == ';':
                    continue

                add_node(t)

    except IOError as err:
        error_and_exit(err)


def parse_model(inputfile):
    global g_model_vars, g_model_arrays

    try:
        num_lines = 0
        with open(inputfile, 'r') as infile:
            for line in infile:
                num_lines += 1

                if num_lines == 1:
                    if "sat" in line:
                        continue
                    else:
                        error_and_exit("formula is not SAT")

                m = re.match(r'([0-9a-zA-Z_]+)(\[([x0-1]+)\])? ([x0-1]+)', line)
                sym = m.group(1)
                index = m.group(3)
                value = m.group(4)

                # choose random value for don't care bits
                if index != None and "x" in index:
                    index = index.replace("x", str(random.randint(0, 1)))

                # choose random value for don't care bits
                if "x" in value:
                    value = value.replace("x", str(random.randint(0, 1)))

                if index is None:
                    assert(sym not in g_model_vars)
                    g_model_vars[sym] = value
                else:
                    if sym not in g_model_arrays: 
                        g_model_arrays[sym] = {}
                    g_model_arrays[sym][index] = value 

        log(1, "parsed {} assignments".format(num_lines))

    except IOError as err:
        error_and_exit(err)

#def add_model():
#    global g_btor, g_model_vars, g_model_arrays, g_nodemap, g_symbolmap
#
#    for sym, value in g_model_vars.items():
#        if sym in g_symbolmap:
#            n = g_symbolmap[sym]
#        else:
#            n = g_nodemap[int(sym)]
#
#        assert(not n.is_array())
#        c = g_btor.Const(value)
#        e = g_btor.Eq(n, c)
#        g_btor.Assert(e)
#
#    for sym, assignments in g_model_arrays.items():
#        if sym in g_symbolmap:
#            n = g_symbolmap[sym]
#        else:
#            n = g_nodemap[int(sym)]
#
#        for index, value in assignments.items():
#            c_i = g_btor.Const(index)
#            c_v = g_btor.Const(value)
#            r = g_btor.Read(n, c_i)
#            e = g_btor.Eq(r, c_v)
#            g_btor.Assert(e)

# TODO: 
#       * formula file should be original btor/smt/smt2
#         - convert formula to btor with boolector -de -rwl 0
#       * formula fully solvable with rewriting (no sat call required)
#       * allow model from stdin for piping models directly
if __name__ == "__main__":
    try:
        (g_options, args) = parse_options()
        formula = args[0]
        model = args[1]

        g_btor = boolector.Boolector()
        parse_model(model)
        parse_btor(formula)

        g_btor.Enable_beta_reduce_all()
        ret = g_btor.Simplify()

        assert(ret == g_btor.Sat())
        if ret == boolector.BOOLECTOR_SAT:
            log(0, "model is valid")
            sys.exit(0)
        else:
            log(0, "model is invalid")
            sys.exit(1)
    except KeyboardInterrupt as err:
        sys.exit(err)
