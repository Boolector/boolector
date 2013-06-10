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

    fun ("lambdax{}".format(cnt),
         [("px{}".format(cnt), bvsort (args.index_bw))],
         bvsort (args.elem_bw),
         "(ite (= ((_ rotate_right 1) i) px{}) "     \
				 "(select a (bvlshr (_ bv1 {}) j)) " \
				 "(select a px{}))".format(cnt, args.index_bw, cnt))
        # "(ite (= ((_ rotate_right 1) i) px{}) "     \
		#		 "(select a ((_ rotate_left 1) j)) " \
		#		 "(select a px{}))".format(cnt, cnt))
        # "(ite (= ((_ rotate_right 1) i) px{}) "     \
		#		 "(select a ((_ rotate_left {}) j)) " \
		#		 "(select a px{}))".format(cnt, args.index_bw - 1, cnt))
    fun ("lambday{}".format(cnt),
         [("py{}".format(cnt), bvsort (args.index_bw))],
         bvsort (args.elem_bw),
         "(ite (= (bvlshr (_ bv1 {}) j) py{}) "       \
				 "(select a ((_ rotate_right 1) i)) " \
				 "(lambdax{} py{}))".format(args.index_bw, cnt, cnt, cnt))
        # "(ite (= ((_ rotate_left 1) j) py{}) "       \
		#		 "(select a ((_ rotate_right 1) i)) " \
		#		 "(lambdax{} py{}))".format(cnt, cnt, cnt))
        # "(ite (= ((_ rotate_left {}) j) py{}) "      \
		#		 "(select a ((_ rotate_right 1) i)) " \
		#		 "(lambdax{} py{}))".format(args.index_bw - 1, cnt, cnt, cnt))
    cnt -= 1

    while cnt:
        fun ("lambdax{}".format(cnt),
             [("px{}".format(cnt), bvsort (args.index_bw))],
             bvsort (args.elem_bw),
             "(ite (= ((_ rotate_right 1) i) px{}) "       \
					 "(lambday{} (bvlshr (_ bv1 {}) j)) " \
					 "(lambday{} px{}))".format(
                 cnt, cnt + 1, args.index_bw, cnt + 1, cnt))
            # "(ite (= ((_ rotate_right 1) i) px{}) "       \
			#		 "(lambday{} ((_ rotate_left 1) j)) " \
			#		 "(lambday{} px{}))".format(
            #     cnt, cnt + 1, cnt + 1, cnt))
            # "(ite (= ((_ rotate_right 1) i) px{}) "       \
			#		 "(lambday{} ((_ rotate_left {}) j)) " \
			#		 "(lambday{} px{}))".format(
            #     cnt, cnt + 1, args.index_bw - 1, cnt + 1, cnt))
        fun ("lambday{}".format(cnt),
             [("py{}".format(cnt), bvsort (args.index_bw))],
             bvsort (args.elem_bw),
             "(ite (= (bvlshr (_ bv1 {}) j) py{}) "      \
			    	 "(lambday{} ((_ rotate_right 1) i))" \
			    	 "(lambdax{} py{}))".format(
                 args.index_bw, cnt, cnt + 1, cnt, cnt))
            # "(ite (= ((_ rotate_left 1) j) py{}) "      \
			#    	 "(lambday{} ((_ rotate_right 1) i))" \
			#    	 "(lambdax{} py{}))".format(
            #     cnt, cnt + 1, cnt, cnt))
             #"(ite (= ((_ rotate_left {}) j) py{}) "      \
			 #   	 "(lambday{} ((_ rotate_right 1) i))" \
			 #   	 "(lambdax{} py{}))".format(
             #    args.index_bw, cnt, cnt + 1, cnt, cnt))
        cnt -= 1

    cmd ("assert", "(not (= i j))")
    cmd ("assert", "(not (= (select a i) (select a j)))")
    cmd ("assert", "(= (lambday1 i) (select a i))")
    cmd ("check-sat")
    cmd ("exit")
         


