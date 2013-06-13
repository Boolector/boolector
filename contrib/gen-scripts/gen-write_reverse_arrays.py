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
    args = aparser.parse_args()

    args.elem_bw = args.index_bw
    max_idx = 2**args.index_bw - 1

    cmd ("set-logic", "QF_AUFBV")
    var ("k", bvsort (args.index_bw))
    var ("a", arsort (args.index_bw, args.elem_bw))

    for i in range(0, max_idx + 1):
        var ("j{}".format(i), bvsort (args.index_bw))

    for i in range(0, max_idx + 1):
        fun ("w{}".format(i), [("p{}".format(i), bvsort (args.index_bw))],
              bvsort (args.elem_bw),
             "(ite (= p{} j{}) j{} ({} p{}))".format(
                 i, i, i, "select a" if not i else "w{}".format(i - 1), i))

    for i in range(0, max_idx + 1):
        fun ("rw{}".format(i), [("p{}".format(i), bvsort (args.index_bw))], 
             bvsort (args.elem_bw),
             "(ite (= p{} (bvsub (_ bv{} {}) j{})) p{} ({} p{}))".format(
                 i, max_idx, args.index_bw, i, i, 
                 "select a" if not i else "rw{}".format(i - 1), i))
    
    print ("(assert (distinct", end ='')
    for i in range(0, max_idx + 1):
        print (" j{}".format(i), end ='')
    print ("))")
    cmd ("assert", "(not (= (w{} k) (rw{} k)))".format(max_idx, max_idx))             
    cmd ("check-sat")
    cmd ("exit")
  
