import os
import pyboolector
from pyboolector import Boolector, BoolectorException

if __name__ == "__main__":
    try:
        # Create Boolector instance
        btor = Boolector()
        # Enable model generation
        btor.Set_opt(pyboolector.BTOR_OPT_MODEL_GEN, True)
        # Create bit-vector sort of size 8
        bvsort8 = btor.BitVecSort(8)
        # Create expressions
        x = btor.Var(bvsort8, "x")
        y = btor.Var(bvsort8, "y")
        zero = btor.Const(0, 8)
        hundred = btor.Const(100, 8)
        # 0 < x
        ult_x = btor.Ult(zero, x)
        btor.Assert(ult_x)
        # x <= 100
        ulte_x = btor.Ulte(x, hundred)
        btor.Assert(ulte_x)
        # 0 < y
        ult_y = btor.Ult(zero, y)
        btor.Assert(ult_y)
        # y <= 100
        ulte_y = btor.Ulte(y, hundred)
        btor.Assert(ulte_y)
        # x * y
        mul = btor.Mul(x, y)
        # x * y < 100
        ult = btor.Ult(mul, hundred)
        btor.Assert(ult)
        umulo = btor.Umulo(x, y)
        numulo = btor.Not(umulo)  # prevent overflow
        btor.Assert(numulo)

        res = btor.Sat()
        print("Expect: sat")
        print("Boolector: ", end='')
        if res == btor.SAT:
            print("sat")
        elif res == btor.UNSAT:
            print("unsat")
        else:
            print("unknown")
        print("")

        # prints "x: 00000100"
        print("assignment of {}: {}".format(x.symbol, x.assignment))
        # prints: "y: 00010101"
        print("assignment of {}: {}".format(y.symbol, y.assignment))
        print("")

        print("Print model in BTOR format:")
        btor.Print_model("btor")
        print("")
        print("Print model in SMT-LIBv2 format:")
        btor.Print_model("smt2")
        print("")
    except BoolectorException as e:
        print("Caught exception: " + str(e))
