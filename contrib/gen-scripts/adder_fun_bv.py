#!/usr/bin/env python3

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
    elem_bw = 1 
    index_bw = 2

    if len(sys.argv) > 1:
        index_bw = int(sys.argv[1])
        if index_bw <= 1:
            index_bw = 2

    cmd("set-logic", "QF_AUFBV")

    var("X", bvsort(index_bw))
    var("Y", bvsort(index_bw))

    print(
"""(define-fun pos ((x (_ BitVec {0:d})) (i (_ BitVec {0:d}))) (_ BitVec 1)
  ((_ extract 0 0) (bvlshr x i)))""".format(index_bw))
    print(
"""(define-fun s ((i (_ BitVec {})) (c_in (_ BitVec 1))) (_ BitVec 1)
  (let ((x (pos X i)) (y (pos Y i)))
    (let ((t1 (bvand (bvand x y) c_in))
          (t2 (bvand (bvand (bvnot x) (bvnot y)) c_in))
          (t3 (bvand (bvand (bvnot x) y) (bvnot c_in)))
          (t4 (bvand (bvand x (bvnot y)) (bvnot c_in))))
      (bvor (bvor (bvor t1 t2) t3) t4))))""".format(index_bw))
    print(
"""(define-fun c_out ((i (_ BitVec {})) (c_in (_ BitVec 1))) (_ BitVec 1)
  (let ((x (pos X i)) (y (pos Y i)))
    (bvor (bvor (bvand x y) (bvand x c_in)) (bvand y c_in))))""".format(
        index_bw))

    max_index = index_bw

    print("(assert");
    print("(let ((i{0:d} (_ bv{0:d} {1:d})) (c_in{0:d} (_ bv0 1)))".format(
          0, index_bw))
    print("(let ((s{0:d} (s i{0:d} c_in{0:d})))".format(0))
    open_par = 3
    for i in range(1, max_index):
        print("(let ((i{0:d} (_ bv{0:d} {1:d})) (c_in{0:d} (c_out i{2:d} c_in{2:d})))".format(i, index_bw, i - 1))
        print("(let ((s{0:d} (s i{0:d} c_in{0:d})))".format(i))
        open_par += 2

    s = "(concat"
    for i in reversed(range(2, max_index)):
        s += " s{} ".format(i)
        s += "(concat"
    s += " s{} s{}".format(1, 0)
    s += ")" * (max_index - 1)

    print("(let ((sum {}))".format(s))
    open_par += 1
    print("(not (= sum (bvadd X Y)))")
    print(")" * open_par)

    cmd("check-sat")
    cmd("exit")
