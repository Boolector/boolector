#!/usr/bin/env python3

import sys

def err(msg):
    print(msg)
    sys.exit(1)

g_prefix = []
g_clauses = []

def dump():
    global g_prefix, g_clauses

    var_map = {}
    lines = []

    print("(set-logic BV)")
    print("(assert")

    # print prefix
    for p in g_prefix:
        type = p[0] 
        if type == "a":
            sympref = "x"
            quant = "forall"
        else:
            assert(type == "e")
            sympref = "y"
            quant = "exists"
        vars = p[1:]
        for v in vars:
            var_map[int(v)] = "{}{}".format(sympref, v)
        vars = " ".join(["({}{} Bool)".format(sympref, v) for v in vars])
        lines.append( "({} ({})".format(quant, vars))
    
    # print clauses
    lines.append("(and")
    for c in g_clauses:
        lits = []
        for l in c:
            lit = int(l)
            var = abs(lit)
            sym = var_map[var]
            assert(sym is not None)
            if lit < 0:
                lits.append("(not {})".format(sym))
            else:
                lits.append(sym)
        if len(lits) == 1:
            lines.append("{}".format(lits[0]))
        else:
            lines.append("(or {})".format(" ".join(lits)))

    # close quantifiers + and + assert
    lines.append(")" * (len(g_prefix) + 2))
    lines.append("(check-sat)")
    lines.append("(exit)")
    print("\n".join(lines))

def parse(infile):
    global g_prefix

    for line in infile:
        t = line.split()
        ch = t[0][0]
        if ch == 'c' or ch == 'p': # skip comments and preamble
            continue
        elif ch == 'a' or ch == 'e': # quantifier prefix
            g_prefix.append(t[:-1])
        else:
            g_clauses.append(t[:-1])


if __name__ == "__main__":

    if len(sys.argv) > 2:
        err("invalid number of arguments (expected one)")

    try:
        if len(sys.argv) < 2:
            parse(sys.stdin)
            dump()
        else:
            with open(sys.argv[1], 'r') as infile:
                parse(infile)
    except IOError as e:
        err(e.msg)
    sys.exit(0)
