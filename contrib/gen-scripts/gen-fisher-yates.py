#! /usr/bin/env python3

from argparse import ArgumentParser

def sexpr(l):
    l = [str(i) for i in l]
    return "({})".format(" ".join(l))

def cmd(tag, string = ""):
    if string == "":
        print(sexpr([tag]))
    else:
        print(sexpr([tag, string]))

def arsort(index_bw, elem_bw):
    return sexpr(["Array", bvsort(index_bw), bvsort(elem_bw)])

def bvsort(bw):
    return sexpr(["_", "BitVec", bw])

def var(sym, sort):
    print("(declare-fun {} () {})".format(sym, sort))

def bvconst(val, bw):
    return "(_ bv{} {})".format(int(val), bw)

def fun(sym, params, sort, term):
    s_params = " ".join(["({} {})".format(p, s) for [p, s] in params])
    print("(define-fun {} ({}) {} {})".format(sym, s_params, sort, term))

def funapp(sym, terms):
    l = [sym]
    l.extend(terms)
    return sexpr(l)


if __name__ == "__main__":

    aparser = ArgumentParser ()
    aparser.add_argument ("index_bw", type=int, help="index bit width")
    aparser.add_argument ("-e", dest="elem_bw", metavar="val", default="32",
                          type=int, help="element bit width (default: 32)")
    aparser.add_argument ("-s", dest="sorted", action="store_true",
                          default=False, 
                          help="pre-initialize array with sorted sequence")
    args = aparser.parse_args()

    max_idx = 2**args.index_bw - 1

    cmd ("set-logic", "QF_AUFBV")
    var ("k", bvsort (args.index_bw))
    var ("a", arsort (args.index_bw, args.elem_bw))
    
    fun ("reverse_a", [("p", bvsort (args.index_bw))], bvsort (args.elem_bw),
         "(select a (bvsub (_ bv{} {}) p))".format(max_idx, args.index_bw))
         
    for i in range(1, max_idx + 1):
        fun ("i{}".format(i), [], bvsort (args.index_bw), 
             "(bvsub (_ bv{} {}) (_ bv{} {}))".format(
                 max_idx, args.index_bw, max_idx - i, args.index_bw))
        
    for i in range(1, max_idx + 1):
        var ("j{}".format(i), bvsort (args.index_bw))

    for i in range(0, max_idx):
        idx = max_idx - i
        fun ("shuffle{}".format(max_idx - i), 
             [("p{}".format(max_idx - i), bvsort (args.index_bw))],
             bvsort (args.elem_bw),
             "(ite (= p{} i{}) ({} j{}) (ite (= p{} j{}) ({} i{}) ({} p{})))" \
             "".format(
                 idx, idx, 
                 "select a" if not i else "shuffle{}".format(idx + 1),
                 idx, idx, idx, 
                 "select a" if not i else "shuffle{}".format(idx + 1),
                 idx, 
                 "select a" if not i else "shuffle{}".format(idx + 1),
                 idx))
        
    for i in range(0, max_idx):
        idx = max_idx - i
        fun ("rshuffle{}".format(max_idx - i), 
             [("p{}".format(max_idx - i), bvsort (args.index_bw))],
             bvsort (args.elem_bw),
             "(ite (= p{} (bvsub (_ bv{} {}) i{})) " \
                  "({} (bvsub (_ bv{} {}) j{})) "    \
                  "(ite (= p{} (bvsub (_ bv{} {}) j{})) " \
                       "({} (bvsub (_ bv{} {}) i{})) ({} p{})))".format(
                           idx, max_idx, args.index_bw, idx,
                           "reverse_a" if not i else "rshuffle{}".format(
                               idx + 1),
                           max_idx, args.index_bw, idx,
                           idx, max_idx, args.index_bw, idx,
                           "reverse_a" if not i else "rshuffle{}".format(
                               idx + 1),
                           max_idx, args.index_bw, idx, 
                           "reverse_a" if not i else "rshuffle{}".format(
                               idx + 1),
                           idx))
        
    fun ("reverse_rshuffle", [("p", bvsort (args.index_bw))],
         bvsort (args.elem_bw), 
         "(rshuffle1 (bvsub (_ bv{} {}) p))".format(max_idx, args.index_bw))

    if args.sorted:
        for i in range(0, max_idx + 1):
            cmd ("assert", "(= (select a (_ bv{} {})) (_ bv{} {}))".format(
                i, args.index_bw, i, args.elem_bw))

    for i in range(1, max_idx + 1):
        cmd ("assert", "(and (bvuge j{} (_ bv0 {})) (bvult j{} i{}))".format(
            i, args.index_bw, i, i))

    cmd ("assert", "(not (= (shuffle1 k) (reverse_rshuffle k)))")
    cmd ("check-sat")
    cmd ("exit")



    
    


