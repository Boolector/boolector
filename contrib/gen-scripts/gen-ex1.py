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
    aparser.add_argument ("n", type=int, help="number of nested lambdas")
    aparser.add_argument ("-i", dest="index_bw", metavar="val",
                          default=32, type=int,
                          help="index bit width (default: 32)")
    aparser.add_argument ("-e", dest="elem_bw", metavar="val",
                          default=32, type=int,
                          help="element bit width (default: 32)")
    args = aparser.parse_args()

    cnt = args.n
    args.index_bw = cnt + 1 if cnt >= args.index_bw else args.index_bw

    cmd ("set-logic", "QF_AUFBV")
    var ("i", bvsort (args.index_bw))
    var ("j", bvsort (args.index_bw))
    var ("a", arsort (args.index_bw, args.elem_bw))

    fun ("lambda{}".format(cnt),
         [("p{}".format(cnt), bvsort (args.index_bw))],
         bvsort (args.elem_bw),
         "(ite (= ((_ extract 0 0) p{}) (_ bv0 1)) "      \
              "(select a (bvadd p{} (_ bv{} {}))) "       \
              "(select a (bvadd (bvadd p{} (_ bv{} {})) " \
              "(bvshl (_ bv{} {}) (_ bv2 {})))))".format(
                        cnt, 
                        cnt, cnt - 1, args.index_bw, 
                        cnt, cnt, args.index_bw, 
                        cnt - 1, args.index_bw, args.index_bw))
    cnt -= 1

    while cnt:
        fun ("lambda{}".format(cnt),
             [("p{}".format(cnt), bvsort (args.index_bw))],
             bvsort (args.elem_bw),
             "(ite (= ((_ extract 0 0) p{}) (_ bv0 1)) "      \
                  "(lambda{} (bvadd p{} (_ bv{} {}))) "       \
                  "(lambda{} (bvadd (bvadd p{} (_ bv{} {})) " \
                  "(bvshl (_ bv{} {}) (_ bv2 {})))))".format(
                       cnt, 
                       cnt + 1, cnt, cnt - 1, args.index_bw, 
                       cnt + 1, cnt, cnt, args.index_bw, 
                       cnt - 1, args.index_bw, args.index_bw))
        cnt -= 1

    #cmd ("assert", "(= ((_ extract 0 0) (lambda1 (bvadd i j))) (_ bv1 1))")
    cmd ("assert", "(= (lambda1 (bvadd i j)) (_ bv42 {}))".format(args.elem_bw))
    cmd ("check-sat")
    cmd ("exit")
         


