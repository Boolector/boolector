from boolector import Boolector

if __name__ == "__main__":
    b = Boolector() 

### Creating Boolector nodes

    # Constants
    _const = b.Const("10010101")
    _zero  = b.Const(0, 128)
    _ones  = b.Const(-1, 129)
    _true  = b.Const(True)
    _false = b.Const(False)
    _one   = b.Const(1, 128)
    _uint  = b.Const(77, 128)
    _int   = b.Const(-77, 128)

    # Variables
    _var   = b.Var(128, "var_symbol")
    _param = b.Param(128, "param_symbol")  # used as function parameters
    _array = b.Array(128, 128, "array_symbol")

    # One's complement  
    _not0    = b.Not(_const)
    _not1    = ~_const

    # Two's complement 
    _neg0    = b.Neg(_zero)
    _neg1    = -_zero

    # Reduction operations on bit vectors
    _redor   = b.Redor(_ones)
    _redxor  = b.Redxor(_one)
    _redand  = b.Redand(_uint)

    # Slicing of bit vectors 
    _slice0  = b.Slice(_param, 8, 0)
    _slice1  = _param[8:0]
    _slice3  = _param[:]   # copy
    _slice2  = _param[8:]  # lower is 0
    _slice4  = _param[:0]  # upper is _param.width - 1
    _slice5  = _param[8]   # extract bit at position 8, equiv. to _param[8:8]
    _slice5  = _param[8:8] # equiv. to _param[8]

    # Unsigned/signed extension
    _uext    = b.Uext(_true, 127)
    _sext    = b.Sext(_false, 127)

    _inc     = b.Inc(_not0)
    _dec     = b.Dec(_not1)
    
    _implies0 = b.Implies(_redor, _redxor) 
    _implies1 = b.Implies(False, _redor)
    _implies2 = b.Implies(True, _redxor)

    _iff0     = b.Iff(True, _redxor)
    _iff1     = b.Iff(_redor, _redxor)
    _iff2     = b.Iff(False, _redxor)

    _xor0     = b.Xor(_uext, _sext)
    _xor1     = _uext ^ _sext
    _xor2     = b.Xor(0xff, _sext)
    _xor3     = 0xff ^ _sext

    _and0     = b.And(_inc, _dec)
    _and1     = b.And(128, _dec)
    _and2     = b.And(_dec, 0xaa)
    _and3     = _dec & 0xaa

    _nand0    = b.Nand(_inc, _dec)
    _nand1    = b.Nand(128, _dec)
    _nand2    = b.Nand(_dec, 0xaa)
    _nand3    = ~(_dec & 0xaa) 

    _or0      = b.Or(_inc, _dec)
    _or1      = b.Or(128, _dec)
    _or2      = b.Or(_dec, 0xaa)
    _or3      = _dec | 0xaa

    _nor0     = b.Nor(_inc, _dec)
    _nor1     = b.Nor(128, _dec)
    _nor2     = b.Nor(_dec, 0xaa)
    _nor3     = ~(_dec | 0xaa) 

    _eq0      = b.Eq(_inc, _dec)
    _eq1      = b.Eq(128, _dec)
    _eq2      = b.Eq(_dec, 0xaa)
    _eq3      = _dec == 0xaa

    _neq0     = b.Ne(_inc, _dec)
    _neq1     = b.Ne(128, _dec)
    _neq2     = b.Ne(_dec, 0xaa)
    _neq3     = _dec != 0xaa

    _add0     = b.Add(_inc, _dec)
    _add1     = b.Add(128, _dec)
    _add2     = b.Add(_dec, 0xaa)
    _add3     = _dec + 0xaa

    _uaddo0   = b.Uaddo(_inc, _dec)
    _uaddo1   = b.Uaddo(128, _dec)
    _uaddo2   = b.Uaddo(_dec, 0xaa)

    _saddo0   = b.Saddo(_inc, _dec)
    _saddo1   = b.Saddo(128, _dec)
    _saddo2   = b.Saddo(_dec, 0xaa)

    _mul0     = b.Mul(_inc, _dec)
    _mul1     = b.Mul(128, _dec)
    _mul2     = b.Mul(_dec, 0xaa)
    _mul3     = _dec * 0xaa

    _umulo0   = b.Umulo(_inc, _dec)
    _umulo1   = b.Umulo(128, _dec)
    _umulo2   = b.Umulo(_dec, 0xaa)

    _smulo0   = b.Smulo(_inc, _dec)
    _smulo1   = b.Smulo(128, _dec)
    _smulo2   = b.Smulo(_dec, 0xaa)

    _ult0     = b.Ult(_inc, _dec)
    _ult1     = b.Ult(128, _dec)
    _ult2     = b.Ult(_dec, 0xaa)
    _ult3     = _dec < 0xaa

    _slt0     = b.Slt(_inc, _dec)
    _slt1     = b.Slt(128, _dec)
    _slt2     = b.Slt(_dec, 0xaa)

    _ulte0    = b.Ulte(_inc, _dec)
    _ulte1    = b.Ulte(128, _dec)
    _ulte2    = b.Ulte(_dec, 0xaa)
    _ulte3    = _dec <= 0xaa

    _slte0    = b.Slte(_inc, _dec)
    _slte1    = b.Slte(128, _dec)
    _slte2    = b.Slte(_dec, 0xaa)

    _ugt0     = b.Ugt(_inc, _dec)
    _ugt1     = b.Ugt(128, _dec)
    _ugt2     = b.Ugt(_dec, 0xaa)
    _ugt3     = _dec > 0xaa

    _sgt0     = b.Sgt(_inc, _dec)
    _sgt1     = b.Sgt(128, _dec)
    _sgt2     = b.Sgt(_dec, 0xaa)

    _ugte0    = b.Ugte(_inc, _dec)
    _ugte1    = b.Ugte(128, _dec)
    _ugte2    = b.Ugte(_dec, 0xaa)
    _ugte3    = _dec >= 0xaa

    _sgte0    = b.Sgte(_inc, _dec)
    _sgte1    = b.Sgte(128, _dec)
    _sgte2    = b.Sgte(_dec, 0xaa)

    _sll0     = b.Sll(_dec, 5)
    _sll1     = b.Sll(_dec, 0b100)
    _sll2     = _dec << 5

    _srl0     = b.Srl(_dec, 5)
    _srl1     = b.Srl(_dec, 0b100)
    _srl2     = _dec >> 5

    _sra0     = b.Sra(_dec, 5)
    _sra1     = b.Sra(_dec, 0b100)

    _rol0     = b.Rol(_dec, 5)
    _rol1     = b.Rol(_dec, 0b100)

    _ror0     = b.Ror(_dec, 5)
    _ror1     = b.Ror(_dec, 0b100)

    _sub0     = b.Sub(_inc, _dec)
    _sub1     = b.Sub(128, _dec)
    _sub2     = b.Sub(_dec, 0xaa)
    _sub3     = _dec - 0xaa

    _ssubo0   = b.Ssubo(_inc, _dec)
    _ssubo1   = b.Ssubo(128, _dec)
    _ssubo2   = b.Ssubo(_dec, 0xaa)

    _udiv0    = b.Udiv(_inc, _dec)
    _udiv1    = b.Udiv(128, _dec)
    _udiv2    = b.Udiv(_dec, 0xaa)
    _udiv3    = _dec / 0xaa

    _urem0    = b.Urem(_inc, _dec)
    _urem1    = b.Urem(128, _dec)
    _urem2    = b.Urem(_dec, 0xaa)
    _urem3    = _dec % 0xaa

    _sdiv0    = b.Sdiv(-_inc, _dec)
    _sdiv1    = b.Sdiv(128, -_dec)
    _sdiv2    = b.Sdiv(_dec, -0xaa)

    _srem0    = b.Srem(-_inc, _dec)
    _srem1    = b.Srem(128, -_dec)
    _srem2    = b.Srem(_dec, -0xaa)

    _sdivo0   = b.Sdivo(-_inc, _dec)
    _sdivo1   = b.Sdivo(128, -_dec)
    _sdivo2   = b.Sdivo(_dec, -0xaa)

    _smod0    = b.Smod(-_inc, _dec)
    _smod1    = b.Smod(128, -_dec)
    _smod2    = b.Smod(_dec, -0xaa)

    # Concatenation of bit vectors
    _concat   = b.Concat(_dec, _inc)

    # Reads on arrays
    _read0    = b.Read(_array, _var) 
    _read1    = b.Read(_array, 12)
    _read2    = _array[_var]
    _read3    = _array[0x1a]

    # Writes on arrays
    _write0   = b.Write(_array, _var, _var) 
    _write1   = b.Write(_array, 10, 0b00001) 

    # If-Then-Else on bit vectors
    _cond0    = b.Cond(_read0[0], _read0, _read1)
    _cond1    = b.Cond(False, _read0, _read1)
    _cond2    = b.Cond(True, 1, _read1)

    # If-Then-Else on arrays 
    _cond3    = b.Cond(0, _write0, _write1)

    # Function
    p0        = b.Param(128)
    p1        = b.Param(128)
    _fun      = b.Fun([p0, p1], b.Cond(p0 < p1, p0, p1))

    # Uninterpreted function
    _boolsort = b.BoolSort()
    _bvsort   = b.BitVecSort(128)
    _funsort  = b.FunSort([_boolsort, _boolsort, _bvsort, _bvsort], _boolsort)
    _uf       = b.UF(_funsort)

    # Function applications
    _apply0   = b.Apply([_var, _var], _fun)
    _apply1   = b.Apply([1, 2], _fun)
    _apply2   = _fun(1, 2)
    _apply3   = b.Apply([_true, _false, _var, _var], _uf)
    _apply4   = b.Apply([1, True, 3, 42], _uf)
    _apply5   = b.Apply([1, False, 3, 42], _uf)
    _apply6   = _uf(1, False, 3, 42)

### Node attributes and methods

    # Get symbol
    s = _var.symbol
    s = _apply4.symbol

    # Set symbol
    _var.symbol = "new_symbol"

    # Get bit width
    w = _apply4.width
    w = _fun.width

    # Get bit width of array index 
    w = _array.index_width

    # Get arity of functions
    a = _fun.arity
    a = _uf.arity

    # Get bit vector representation of constants as string
    bits = _const.bits

    # Dump nodes to stdout or files (default format is BTOR) 
    _apply4.Dump()
    # Dump to file 'dump.btor'
    _apply4.Dump(outfile="dump.btor")
    _apply4.Dump("smt1")
    _apply4.Dump("smt2")
    # Dump to file 'dump.smt2'
#    _apply4.Dump("smt2", "dump.smt2")

### Boolector methods

    # Available options
    b.Options()
    # Print available options
    print("Available Boolector options:")
    print("\n".join(["  " + str(o) for o in b.Options()]))

    # Set options
    b.Set_opt("incremental", 1)
    b.Set_opt("model_gen", 1)

    # Get options
    o = b.Get_opt("model_gen")
#    print(o.lng)  # long option name
#    print(o.shrt) # short option name
#    print(o.desc) # description
#    print(o.min)  # min value
#    print(o.max)  # max value
#    print(o.dflt) # default value
#    print(o.val)  # current value

    # Set SAT solver (can only be done before the first Sat() call)
    # Lingeling is the default SAT solver
    b.Set_sat_solver("MiniSAT")
    
    # Assert formulas
    b.Assert(_cond0[1])
    b.Assert(_apply5 != _apply3)

    # Assume formulas
    b.Assume(_cond1[1])

    # Run simplification separately
    res = b.Simplify()

    # Clone boolector instance 'b'
    bb = b.Clone()

    # Check sat
    res = b.Sat()
    # Check sat with limits
#    res = b.Sat(100, 10000)
#    res = b.Sat(lod_limit=100, sat_limit=10000)

    # Get model or query assignments for nodes
    if res == b.SAT:
        # Get model and print to stdout
        b.Print_model()
        # Get model and print to file 'model.out'
#        b.Print_model("model.out")

         # Query assignments
#        print("Query assignments:")
#        print("{} {}".format(_var.symbol, _var.assignment))
#        print("{} {}".format(_array.symbol, _array.assignment))
#        print("{} {}".format(_uf.symbol, _uf.assignment))

    # Get matching node of _cond0 in clone 'bb'
    _cond0_matched = bb.Match(_cond0)
    # Assume
    bb.Assume(~_cond0_matched[1])
    bb.Assume(_cond0_matched[2])
    # Check sat
    res = bb.Sat()

    if res == b.UNSAT:
        # Check if assumptions are failed
        bb.Failed(~_cond0_matched[1])
        bb.Failed(_cond0_matched[2])

