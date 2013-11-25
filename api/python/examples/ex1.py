#! /usr/bin/env python3

from boolector import Boolector

if __name__ == "__main__":

    b = Boolector()

    x = b.Var(32)
    y = b.Var(32)
    
    b.Assert(x + y < y)
    ret = b.Sat()
    print(ret)

