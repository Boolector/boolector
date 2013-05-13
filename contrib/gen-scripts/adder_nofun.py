#!/usr/bin/env python3

import math
import sys

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

def let(varbinds, term):
    s_varbinds = " ".join(["({} {})".format(v, t) for [v, t] in varbinds])
    return sexpr(["let", s_varbinds, term])

if __name__ == "__main__":
    if len(sys.argv) > 1:
        bw = int(sys.argv[1])
        bw = int(math.pow(2, int(math.log2(bw) + 0.5)))
        if bw <= 1:
            bw = 2
    else:
        bw = 2

    elem_bw = 1 
    index_bw = int(math.log2(bw))

    cmd("set-logic", "QF_AUFBV")
    cmd("set-info", ":status unsat")

    var("a", arsort(index_bw, elem_bw))
    var("b", arsort(index_bw, elem_bw))
    var("X", bvsort(bw))
    var("Y", bvsort(bw))

    print(
"""(define-fun s ((i (_ BitVec {})) (c_in (_ BitVec 1))) (_ BitVec 1)
  (let ((x (select a i)) (y (select b i)))
    (let ((t1 (bvand (bvand x y) c_in))
          (t2 (bvand (bvand (bvnot x) (bvnot y)) c_in))
          (t3 (bvand (bvand (bvnot x) y) (bvnot c_in)))
          (t4 (bvand (bvand x (bvnot y)) (bvnot c_in))))
      (bvor (bvor (bvor t1 t2) t3) t4))))""".format(index_bw))
    print(
"""(define-fun c_out ((i (_ BitVec {})) (c_in (_ BitVec 1))) (_ BitVec 1)
  (let ((x (select a i)) (y (select b i)))
    (bvor (bvor (bvand x y) (bvand x c_in)) (bvand y c_in))))""".format(
        index_bw))

    max_index = 2 ** index_bw

    for a, v in (["a", "X"], ["b", "Y"]):
        print("(assert (= {} ".format(v), end='')
        s = "(concat"
        for i in range(max_index - 2):
            s += " (select {} (_ bv{} {}))".format(a, i, index_bw)
            s += " (concat"
        s += " (select {2:s} (_ bv{1:d} {0:d}))".format(
                index_bw, max_index - 2, a)  
        s += " (select {2:s} (_ bv{1:d} {0:d}))".format(
                index_bw, max_index - 1, a)  
        s += ")" * (max_index - 1) # close concats
        s += "))" # close assert, eq
        print(s)


    print("(assert");
    print(
"""(let ((i{0:d} (_ bv{0:d} {1:d})))
    (let ((x{0:d} (select a i{0:d})) (y{0:d} (select b i{0:d})))
     (let ((c_in{0:d} (_ bv0 1)))
      (let ((t1_{0:d} (bvand (bvand x{0:d} y{0:d}) c_in{0:d}))
            (t2_{0:d} (bvand (bvand (bvnot x{0:d}) (bvnot y{0:d})) c_in{0:d}))
            (t3_{0:d} (bvand (bvand (bvnot x{0:d}) y{0:d}) (bvnot c_in{0:d})))
            (t4_{0:d} (bvand (bvand x{0:d} (bvnot y{0:d})) (bvnot c_in{0:d}))))
       (let ((s{0:d} (bvor (bvor (bvor t1_{0:d} t2_{0:d}) t3_{0:d}) t4_{0:d})))
""".format(max_index - 1, index_bw)) 

    open_par = 6
    for i in reversed(range(max_index - 1)):
        print(
"""(let ((i{0:d} (_ bv{0:d} {1:d})))
    (let ((x{0:d} (select a i{0:d})) (y{0:d} (select b i{0:d})))
     (let ((c_in{0:d} (bvor (bvor (bvand x{2:d} y{2:d}) (bvand x{2:d} c_in{2:d})) (bvand y{2:d} c_in{2:d}))))
      (let ((t1_{0:d} (bvand (bvand x{0:d} y{0:d}) c_in{0:d}))
            (t2_{0:d} (bvand (bvand (bvnot x{0:d}) (bvnot y{0:d})) c_in{0:d}))
            (t3_{0:d} (bvand (bvand (bvnot x{0:d}) y{0:d}) (bvnot c_in{0:d})))
            (t4_{0:d} (bvand (bvand x{0:d} (bvnot y{0:d})) (bvnot c_in{0:d}))))
       (let ((s{0:d} (bvor (bvor (bvor t1_{0:d} t2_{0:d}) t3_{0:d}) t4_{0:d})))
""".format(i, index_bw, i + 1)) 
        open_par += 5

    s = "(concat"
    for i in range(max_index - 2):
        s += " s{} ".format(i)
        s += "(concat"
    s += " s{} s{}".format(max_index - 2, max_index - 1) 
    s += ")" * (max_index - 1)

    print("(let ((sum {}))".format(s))
    open_par += 1
    print("(not (= sum (bvadd X Y)))")
    print(")" * open_par)

    cmd("check-sat")
    cmd("exit")
