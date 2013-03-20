#ifndef IBitVector_h_INCLUDED
#define IBitVector_h_INCLUDED

// This class defines the BitVector API interface
class IBitVector
{
 public:
  // Represents a reference to a single bit of a data entity
  struct Bit
  {
    Bit () : m_nId (0), m_nBit (0) {}

    Bit (unsigned nId, unsigned nBit)
        :

          m_nId (nId),
          m_nBit (nBit)
    {
    }

    bool operator== (const Bit& other) const
    {
      return ((m_nId == other.m_nId) && (m_nBit == other.m_nBit));
    }

    bool operator!= (const Bit& other) const { return !(*this == other); }

    // ID of the referenced data entity
    unsigned m_nId;

    // Bit of the data entity
    unsigned m_nBit;
  };

  // Represents a reference to a bit range of a data entity
  struct BitRange
  {
    BitRange () : m_nId (0), m_nMsb (0), m_nLsb (0) {}

    BitRange (unsigned nId, unsigned nMsb, unsigned nLsb)
        :

          m_nId (nId),
          m_nMsb (nMsb),
          m_nLsb (nLsb)
    {
      // LSB should be numerically less or equal to the MSB
      assert (m_nMsb >= m_nLsb);
    }

    unsigned getWidth () const { return (m_nMsb - m_nLsb + 1); }

    bool operator== (const BitRange& other) const
    {
      return ((m_nId == other.m_nId) && (m_nMsb == other.m_nMsb)
              && (m_nLsb == other.m_nLsb));
    }

    bool operator!= (const BitRange& other) const { return !(*this == other); }

    // ID of the referenced data entity
    unsigned m_nId;

    // MSB of the referenced range of the data entity.
    // MSB should be numerically less than the width of the referenced data
    // entity.
    unsigned m_nMsb;

    // LSB of the referenced range of the data entity.
    // LSB should be numerically less than the width of the referenced data
    // entity.
    unsigned m_nLsb;
  };

 public:
  // Method addVariable
  //
  // Declares a variable
  //
  // There is no requirement to either assign all bits of the variable
  // or to leave all of them unassigned. Some bits may be assigned and some
  // may be not. Any bit that is assigned should be assigned at most once.
  // Multiple assignments to the same bit are not allowed.
  //
  // There is no requirement for the variables not to be assigned in a loop,
  // like in a = b, b = a. However, the tool generating the BitVector API
  // model may optionally assure that no such loops are created.
  //
  // The names of the variables are not required to be unique. However, the
  // tool generating the BitVector API model may optionally assure that the
  // names of all variables are unique.
  //
  // Arguments
  //
  // nId - unique ID of the variable
  // strName - name of the variable
  // nWidth - bit width of the variable
  //
  // bIsNextStateVariable - when a sequential (vs. combinational) BitVector
  //     model is created, for each source level variable, either one or two
  //     BitVector variables are added. One BitVector variable represents the
  //     current state of the corresponding source level variable, and the
  //     other represents the next state of that variable. This boolean
  //     argument specifies whether the BitVector variable being added is the
  //     one representing the current state or the next state of the
  //     corresponding source level variable.
  //         The variable representing the current state variable is added if
  //     either the current state variable or the next state variable are
  //     referenced in the model. The variable representing the next state
  //     variable is added only if the next state variable specifically is
  //     referenced.
  //         If the variable representing the next state variable is added in
  //     addition to adding the current state variable, the two calls to
  //     addVariable() are followed by one or more calls to addState() and/or
  //     addNonState() methods. Each bit of the declared variable should be
  //     referenced by the arguments of one of these calls.
  //         The value of this argument is false if a combinational (vs.
  //     sequential) BitVector model is created.
  //
  //  bIsLoopBreakingVariable - specifies whether the variable is a special
  //     variable created in order to break loops in the model. The value of
  //     this argument is false if loop breaking is not performed while
  //     creating the BitVector model.
  //
  //  bIsStateRetainVariable - specifies whether the variable is a special
  //     variable created in order to model the retain value of a state
  //     signal.
  //
  //  eDirection - direction of the variable. The value of this argument is
  //     typically irrelevant if a flat (non-hierarchical) BitVector model is
  //     created.
  //
  // Preconditions
  //
  // 1. No other declaration with the same ID should be previously made.
  // 2. nWidth should be greater than 0.
  virtual void addVariable (unsigned nId,
                            const string& strName,
                            unsigned nWidth,
                            bool bIsNextStateVariable            = false,
                            bool bIsLoopBreakingVariable         = false,
                            bool bIsStateRetainVariable          = false,
                            IBitVector::DirectionKind eDirection = INTERNAL)
  {
    assert (false);
  }

  // Method addRangeName
  //
  // Declares a name for a specific range of a variable
  //
  // This method is optional, and is primarily useful for debugging purposes.
  // It provides a way to pass information about original variable names to
  // the BitVector API level. The names of the variables provided as a part
  // of the addVariable() method may be insufficient in order to reconstruct
  // the original variable names, since the information about data types of
  // the original variables is lost during data type linearization performed
  // prior to the creation of the BitVector variables. For example, names of
  // struct members cannot be passed and are not passed as a part of
  // addVariable() interface. This method provides the missing information
  // about the original names.
  //
  // Arguments
  //
  // bitRange - range of a BitVector variable to be assigned a name.
  //
  // strRangeName - name to be assigned to the given BitVector range. For
  //     example, if bitRange.m_nId is an ID of a variable named "v" which
  //     was originally declared as a variable with a struct type, and
  //     bitRange.m_nMsb/bitRange.m_nLsb corresponds to a selection of a
  //     struct member named "m1" in that struct, the strRangeName may be
  //     the "v.m1" string.
  //
  // nRangeMsb/nRangeLsb - MSB and LSB of the original declaration of the
  //     given BitVector range. For example, if the given variable was
  //     originally declared as "bit [5:2] b;", the
  //     bitRange.m_nMsb/bitRange.m_nLsb will be [3:0] (linearized range with
  //     LSB normalized to 0), while nRangeMsb/nRangeLsb will be [5:2]
  //     (original declaration range). nRangeMsb/nRangeLsb may be used to
  //     reconstruct the original indexes used to refer to the original
  //     variables. If the given variable was originally declared with a
  //     builtin type (for example, it was declared as "bit b;" or "int b;"),
  //     nRangeMsb/nRangeLsb will be initialized with the linearized range of
  //     the type (nRangeMsb will be set to type's width minus 1 and
  //     nRangeLsb will be 0).
  //
  // Preconditions
  //
  // 1. ID referenced by bitRange should be previously declared using
  //    addVariable().
  // 2. (bitRange.m_nMsb - bitRange.m_nLsb) == (nRangeMsb - nRangeLsb).
  virtual void addRangeName (IBitVector::BitRange bitRange,
                             const string& strRangeName,
                             unsigned nRangeMsb,
                             unsigned nRangeLsb)
  {
    // The default implementation is empty, as to not require all
    // implementations of IBitVector to implement this method
  }

  // Method addState
  //
  // This method should be called only if sequential (vs. combinational)
  // BitVector model is created.
  //
  // The method specifies what range of the given variable represents a
  // state, and what ranges of other variables represent the initial value and
  // the next state function of the state.
  //
  // If the given variable has several ranges that represent state, the method
  // is called several times, once for each such range.
  //
  // Arguments
  //
  // variable - bit range of the variable which should be treated as a state.
  //
  // initValue - bit range of the variable representing the initial value
  //     of the state specified by the "variable" argument. The variable
  //     referenced by this argument is typically is constant, although it
  //     is not limited to be a constant. If the state has no initial value,
  //     the ID of the variable referenced by this argument should be 0.
  //
  // nextState - bit range of the variable representing the next state
  //     function of the "variable" argument. This variable is required to be
  //     valid (should not have ID 0).
  //
  // Preconditions
  //
  // 1. All referenced data entities should be previously declared.
  // 2. Widths of ranges of all referenced data entities should be the same.
  virtual void addState (IBitVector::BitRange variable,
                         IBitVector::BitRange initValue,
                         IBitVector::BitRange nextState)
  {
    assert (false);
  }

  // Method addNonState
  //
  // This method should be called only if sequential (vs. combinational)
  // BitVector model is created.
  //
  // The method specifies what range of the given variable represents a
  // non-state, and what range of other variable represents the next state
  // value of this non-state, if such variable exists.
  //
  // If the given variable has several ranges that represent non-state, the
  // method is called several times, once for each such range.
  //
  // Arguments
  //
  // variable - bit range of the variable which should be treated as a
  //     non-state.
  //
  // nextState - bit range of the variable which represents the next state
  //     value of the "variable" argument. If no variable representing the
  //     next state value of the "variable" argument is present in the model,
  //     the ID of the variable referenced by this argument should be 0.
  //
  // Preconditions
  //
  // 1. The two referenced data entities should be previously declared.
  // 2. Widths of ranges of the two referenced data entities should be the
  //    same.
  virtual void addNonState (IBitVector::BitRange variable,
                            IBitVector::BitRange nextState)
  {
    assert (false);
  }

  // Method addConstant
  //
  // Declares a constant
  //
  // There is no requirement that the values of all constants should be
  // different. However, the tool generating the BitVector API model may
  // optionally assure that no two constants with the same value are created.
  //
  // Arguments
  //
  // nId - unique ID of the constant.
  //
  // strValue - value of the constant. The size of the string should match the
  //      bit width of the constant. Each character of the string should
  //      represent a single binary digit. The allowed values are '0', '1'
  //      and 'x'. The first character of the string denotes the MSB of the
  //      value, and the last character denotes the LSB.
  //
  // nWidth - bit width of the constant. The width should match the length
  //      of the strValue string.
  //
  // Preconditions
  //
  // 1. No other declaration with the same ID should be previously made.
  virtual void addConstant (unsigned nId,
                            const string& strValue,
                            unsigned nWidth)
  {
    assert (false);
  }

  // Method addAssignment
  //
  // Copies a bit vector
  //
  // output = input
  //
  // Arguments
  //
  // output - output of the assignment
  // input - input of the assignment
  //
  // Preconditions
  //
  // 1. The two referenced data entities should be previously declared.
  // 2. Widths of ranges of the two referenced data entities should be the
  //    same.
  virtual void addAssignment (IBitVector::BitRange output,
                              IBitVector::BitRange input)
  {
    assert (false);
  }

  // Method addBitOr
  //
  // Performs bit-wise OR of two bit vectors
  //
  // output = firstOperand | secondOperand
  //
  // Arguments
  //
  // output - output of the operation
  // firstOperand - first operand of the operation
  // secondOperand - second operand of the operation
  //
  // Preconditions
  //
  // 1. All referenced data entities should be previously declared.
  // 2. Widths of ranges of all referenced data entities should be the same.
  virtual void addBitOr (IBitVector::BitRange output,
                         IBitVector::BitRange firstOperand,
                         IBitVector::BitRange secondOperand)
  {
    assert (false);
  }

  // Method addBitAnd
  //
  // Performs bit-wise AND of two bit vectors
  //
  // output = firstOperand & secondOperand
  //
  // Arguments
  //
  // output - output of the operation
  // firstOperand - first operand of the operation
  // secondOperand - second operand of the operation
  //
  // Preconditions
  //
  // 1. All referenced data entities should be previously declared.
  // 2. Widths of ranges of all referenced data entities should be the same.
  virtual void addBitAnd (IBitVector::BitRange output,
                          IBitVector::BitRange firstOperand,
                          IBitVector::BitRange secondOperand)
  {
    assert (false);
  }

  // Method addBitXor
  //
  // Performs bit-wise XOR of two bit vectors
  //
  // output = firstOperand ^ secondOperand
  //
  // Arguments
  //
  // output - output of the operation
  // firstOperand - first operand of the operation
  // secondOperand - second operand of the operation
  //
  // Preconditions
  //
  // 1. All referenced data entities should be previously declared.
  // 2. Widths of ranges of all referenced data entities should be the same.
  virtual void addBitXor (IBitVector::BitRange output,
                          IBitVector::BitRange firstOperand,
                          IBitVector::BitRange secondOperand)
  {
    assert (false);
  }

  // Method addBitNot
  //
  // Negates every bit in a bit vector
  //
  // output = !operand
  //
  // Arguments
  //
  // output - output of the operation
  // operand - operand of the operation
  //
  // Preconditions
  //
  // 1. The two referenced data entities should be previously declared.
  // 2. Widths of ranges of the two referenced data entities should be the same.
  virtual void addBitNot (IBitVector::BitRange output,
                          IBitVector::BitRange operand)
  {
    assert (false);
  }

  // Method addConcat
  //
  // Concatenates one or more bit vectors
  //
  // output = { operands[0], operands[1], ... operands[N - 1] }
  //
  // Arguments
  //
  // output - output of the operation
  // operands - operands of the operation
  //
  // Preconditions
  //
  // 1. All referenced data entities should be previously declared.
  // 2. The sum of widths of the referenced ranges of the operands should be
  //    equal to the width of the referenced range of output.
  virtual void addConcat (IBitVector::BitRange output,
                          const vector<BitRange>& operands)
  {
    assert (false);
  }

  // Method addReplicate
  //
  // Concatenates a bit vector to itself the specified number of times
  //
  // output = { replicationCount { input }}
  //
  // Arguments
  //
  // output - output of the operation
  // operand - operand of the operation
  // nReplicationCount - number of times to replicate the operand
  //
  // Preconditions
  //
  // 1. All referenced data entities should be previously declared.
  // 2. The width of the referenced range of the output should be the same
  //    as the width of the referenced range of the input multiplied by
  //    nReplicationCount.
  virtual void addReplicate (IBitVector::BitRange output,
                             IBitVector::BitRange operand,
                             unsigned nReplicationCount)
  {
    assert (false);
  }

  // Method addEqual
  //
  // Checks whether two bit vectors are equal
  //
  // output = (firstOperand == secondOperand)
  //
  // Arguments
  //
  // output - output of the operation
  // firstOperand - first operand of the operation
  // secondOperand - second operand of the operation
  //
  // Preconditions
  //
  // 1. All referenced data entities should be previously declared.
  // 2. The width of the referenced range of output should be 1.
  // 3. Widths of ranges of firstOperand and secondOperand should be the same.
  virtual void addEqual (IBitVector::BitRange output,
                         IBitVector::BitRange firstOperand,
                         IBitVector::BitRange secondOperand)
  {
    assert (false);
  }

  // Method addGreaterThan
  //
  // Checks whether a bit vector is greater than another.
  // The operator treats its operands as unsigned values.
  //
  // output = (firstOperand > secondOperand)
  //
  // Arguments
  //
  // output - output of the operation
  // firstOperand - first operand of the operation
  // secondOperand - second operand of the operation
  //
  // Preconditions
  //
  // 1. All referenced data entities should be previously declared
  // 2. The width of the referenced range of output should be 1.
  // 3. Widths of ranges of firstOperand and secondOperand should be the same.
  virtual void addGreaterThan (IBitVector::BitRange output,
                               IBitVector::BitRange firstOperand,
                               IBitVector::BitRange secondOperand)
  {
    assert (false);
  }

  // Method addGreaterEqual
  //
  // Checks whether a bit vector is greater than or equal to another.
  // The operator treats its operands as unsigned values.
  //
  // output = (firstOperand >= secondOperand)
  //
  // Arguments
  //
  // output - output of the operation
  // firstOperand - first operand of the operation
  // secondOperand - second operand of the operation
  //
  // Preconditions
  //
  // 1. All referenced data entities should be previously declared.
  // 2. The width of the referenced range of output should be 1.
  // 3. Widths of ranges of firstOperand and secondOperand should be the same.
  virtual void addGreaterEqual (IBitVector::BitRange output,
                                IBitVector::BitRange firstOperand,
                                IBitVector::BitRange secondOperand)
  {
    assert (false);
  }

  // Method addLessThan
  //
  // Checks whether a bit vector is less than another.
  // The operator treats its operands as unsigned values.
  //
  // output = (firstOperand < secondOperand)
  //
  // Arguments
  //
  // output - output of the operation
  // firstOperand - first operand of the operation
  // secondOperand - second operand of the operation
  //
  // Preconditions
  //
  // 1. All referenced data entities should be previously declared.
  // 2. The width of the referenced range of output should be 1.
  // 3. Widths of ranges of firstOperand and secondOperand should be the same.
  virtual void addLessThan (IBitVector::BitRange output,
                            IBitVector::BitRange firstOperand,
                            IBitVector::BitRange secondOperand)
  {
    assert (false);
  }

  // Method addLessEqual
  //
  // Checks whether a bit vector is less than or equal to another.
  // The operator treats its operands as unsigned values.
  //
  // output = (firstOperand <= secondOperand)
  //
  // Arguments
  //
  // output - output of the operation
  // firstOperand - first operand of the operation
  // secondOperand - second operand of the operation
  //
  // Preconditions
  //
  // 1. All referenced data entities should be previously declared.
  // 2. The width of the referenced range of output should be 1.
  // 3. Widths of ranges of firstOperand and secondOperand should be the same.
  virtual void addLessEqual (IBitVector::BitRange output,
                             IBitVector::BitRange firstOperand,
                             IBitVector::BitRange secondOperand)
  {
    assert (false);
  }

  // Method addLogicalAnd
  //
  // Performs logical AND of two bit vectors
  //
  // output = firstOperand && secondOperand
  //
  // Arguments
  //
  // output - output of the operation
  // firstOperand - first operand of the operation
  // secondOperand - second operand of the operation
  //
  // Preconditions
  //
  // 1. All referenced data entities should be previously declared.
  // 2. The width of the referenced range of output should be 1.
  virtual void addLogicalAnd (IBitVector::BitRange output,
                              IBitVector::BitRange firstOperand,
                              IBitVector::BitRange secondOperand)
  {
    assert (false);
  }

  // Method addLogicalOr
  //
  // Performs logical OR of two bit vectors
  //
  // output = firstOperand || secondOperand
  //
  // Arguments
  //
  // output - output of the operation
  // firstOperand - first operand of the operation
  // secondOperand - second operand of the operation
  //
  // Preconditions
  //
  // 1. All referenced data entities should be previously declared.
  // 2. The width of the referenced range of output should be 1.
  virtual void addLogicalOr (IBitVector::BitRange output,
                             IBitVector::BitRange firstOperand,
                             IBitVector::BitRange secondOperand)
  {
    assert (false);
  }

  // Method addLogicalNot
  //
  // Performs logical negation
  //
  // output = !input
  //
  // Arguments
  //
  // output - output of the operation
  // operand - operand of the operation
  //
  // Preconditions
  //
  // 1. The two referenced data entities should be previously declared.
  // 2. The width of the referenced range of output should be 1.
  virtual void addLogicalNot (IBitVector::BitRange output,
                              IBitVector::BitRange operand)
  {
    assert (false);
  }

  // Method addSum
  //
  // Adds two bit vectors
  //
  // output = firstOperand + secondOperand
  //
  // Arguments
  //
  // output - output of the operation
  // firstOperand - first operand of the operation
  // secondOperand - second operand of the operation
  //
  // Preconditions
  //
  // 1. All referenced data entities should be previously declared.
  // 2. Widths of ranges of all referenced data entities should be the same.
  virtual void addSum (IBitVector::BitRange output,
                       IBitVector::BitRange firstOperand,
                       IBitVector::BitRange secondOperand)
  {
    assert (false);
  }

  // Method addSub
  //
  // Subtracts two bit vectors
  //
  // output = firstOperand - secondOperand
  //
  // Arguments
  //
  // output - output of the operation
  // firstOperand - first operand of the operation
  // secondOperand - second operand of the operation
  //
  // Preconditions
  //
  // 1. All referenced data entities should be previously declared.
  // 2. Widths of ranges of all referenced data entities should be the same.
  virtual void addSub (IBitVector::BitRange output,
                       IBitVector::BitRange firstOperand,
                       IBitVector::BitRange secondOperand)
  {
    assert (false);
  }

  // Method addMul
  //
  // Mutliplies two bit vectors
  //
  // output = firstOperand * secondOperand
  //
  // Arguments
  //
  // output - output of the operation
  // firstOperand - first operand of the operation
  // secondOperand - second operand of the operation
  //
  // Preconditions
  //
  // 1. All referenced data entities should be previously declared.
  // 2. Widths of ranges of all referenced data entities should be the same.
  virtual void addMul (IBitVector::BitRange output,
                       IBitVector::BitRange firstOperand,
                       IBitVector::BitRange secondOperand)
  {
    assert (false);
  }

  // Method addDiv
  //
  // Performs division between two bit vectors.
  // The operator treats its operands as unsigned values.
  //
  // output = firstOperand / secondOperand
  //
  // Arguments
  //
  // output - output of the operation
  // firstOperand - first operand of the operation
  // secondOperand - second operand of the operation
  //
  // Preconditions
  //
  // 1. All referenced data entities should be previously declared.
  // 2. Widths of ranges of all referenced data entities should be the same.
  virtual void addDiv (IBitVector::BitRange output,
                       IBitVector::BitRange firstOperand,
                       IBitVector::BitRange secondOperand)
  {
    assert (false);
  }

  // Method addMod
  //
  // Computes firstOperand modulo secondOperand
  // The operator treats its operands as unsigned values.
  //
  // output = firstOperand % secondOperand
  //
  // Arguments
  //
  // output - output of the operation
  // firstOperand - first operand of the operation
  // secondOperand - second operand of the operation
  //
  // Preconditions
  //
  // 1. All referenced data entities should be previously declared.
  // 2. Widths of ranges of all referenced data entities should be the same.
  virtual void addMod (IBitVector::BitRange output,
                       IBitVector::BitRange firstOperand,
                       IBitVector::BitRange secondOperand)
  {
    assert (false);
  }

  // Method addLShift
  //
  // Shifts the bits in a bit vector to the left by a constant amount of bits
  //
  // output = operand << nShiftAmount
  //
  // Arguments
  //
  // output - output of the operation
  // operand - operand of the operation
  // nShiftAmount - shift amount
  //
  // Preconditions
  //
  // 1. The two referenced data entities should be previously declared.
  // 2. Widths of ranges of the two referenced data entities should be the
  //    same.
  virtual void addLShift (IBitVector::BitRange output,
                          IBitVector::BitRange operand,
                          unsigned nShiftAmount)
  {
    assert (false);
  }

  // Method addRShift
  //
  // Shifts the bits in a bit vector to the right by a constant amount of
  // bits. The operation is logical, not arithmetic, meaning that the vacant
  // bits on the left are filled with zeros.
  //
  // output = operand >> nShiftAmount
  //
  // Arguments
  //
  // output - output of the operation
  // operand - operand of the operation
  // nShiftAmount - shift amount
  //
  // Preconditions
  //
  // 1. The two referenced data entities should be previously declared.
  // 2. Widths of ranges of the two referenced data entities should be the
  //    same.
  virtual void addRShift (IBitVector::BitRange output,
                          IBitVector::BitRange operand,
                          unsigned nShiftAmount)
  {
    assert (false);
  }

  // Method addLShiftNonConst
  //
  // Shifts the bits in a bit vector to the left by a non-constant amount of
  // bits
  //
  // output = operand << shiftAmount
  //
  // Arguments
  //
  // output - output of the operation
  // operand - operand of the operation
  // shiftAmount - shift amount
  //
  // Preconditions
  //
  // 1. The three referenced data entities should be previously declared.
  // 2. Width of output and operand should be the same. Width of shiftAmount
  //    may be different.
  virtual void addLShiftNonConst (IBitVector::BitRange output,
                                  IBitVector::BitRange operand,
                                  IBitVector::BitRange shiftAmount)
  {
    assert (false);
  }

  // Method addRShiftNonConst
  //
  // Shifts the bits in a bit vector to the right by a non-constant amount of
  // bits. The operation is logical, not arithmetic, meaning that the vacant
  // bits on the left are filled with zeros.
  //
  // output = operand >> shiftAmount
  //
  // Arguments
  //
  // output - output of the operation
  // operand - operand of the operation
  // shiftAmount - shift amount
  //
  // Preconditions
  //
  // 1. The three referenced data entities should be previously declared.
  // 2. Width of output and operand should be the same. Width of shiftAmount
  //    may be different.
  virtual void addRShiftNonConst (IBitVector::BitRange output,
                                  IBitVector::BitRange operand,
                                  IBitVector::BitRange shiftAmount)
  {
    assert (false);
  }

  // Method addCondition
  //
  // Adds a conditional operator (an if-then-else)
  //
  // There are two forms of the conditional operator. In one form, the
  // condition is a boolean (conditionOperand.m_nMsb ==
  // conditionOperand.m_nLsb) and the semantics of the operator is as follows:
  //
  // if conditionOperand.m_nId[conditionOperand.m_nLsb] = '1' then
  //    output = thenOperand;
  // else
  //    output = elseOperand;
  // end if
  //
  // In the second form, the condition is a bit-vector having the same width
  // as the output ((conditionOperand.m_nMsb - conditionOperand.m_nLsb) =
  // (output.m_nMsb - output.m_nLsb)). In this form, the semantics of the
  // operator is that each bit of the condition controls the assignment of
  // the corresponding bits of the inputs:
  //
  // For each i = 0 to (output.m_nMsb - output.m_nLsb):
  //
  // if conditionOperand.m_nId[conditionOperand.m_nLsb + i] = '1' then
  //     output.m_nId[output.m_nLsb + i] =
  //         thenOperand.m_nId[thenOperand.m_nLsb + i];
  // else
  //     output.m_nId[output.m_nLsb + i] =
  //         elseOperand.m_nId[elseOperand.m_nLsb + i];
  // end if
  //
  // Arguments
  //
  // output - output of the operation
  // conditionOperand - condition of the operation
  // thenOperand - "then" operand of the operation
  // elseOperand - "else" operand of the operation
  //
  // Preconditions
  //
  // 1. All referenced data entities should be previously declared.
  // 2. Widths of ranges of all referenced data entities except
  //    conditionOperand should be the same. The width of referenced range of
  //    conditionOperand should be either 1 or be the same as the widths
  //    of other referenced data entities.
  virtual void addCondition (IBitVector::BitRange output,
                             IBitVector::BitRange conditionOperand,
                             IBitVector::BitRange thenOperand,
                             IBitVector::BitRange elseOperand)
  {
    assert (false);
  }

  // Method addCase
  //
  // Adds a case operator
  //
  // The case operator has the following general structure:
  //
  // output = case
  //    operands[0] : operands[1];
  //    operands[2] : operands[3];
  //    operands[4] : operands[5];
  //    ...
  //    operands[N - 2] : operands[N - 1];
  //
  // In this representation, the variables with even indexes (operands[0],
  // operands[2], etc.) are called "conditions", while the variables with
  // odd indexes (operands[1], operands[3], etc.) are called "data".
  //
  // The width of the output and the width of all data should match.
  // The width of the conditions should either match the width of the output
  // (and the data) or should be 1 (the condition is a boolean value). There
  // is no requirement for all conditions to either all match the width of
  // the output or to be all 1. Some of them may match the width of the
  // output and some may have width 1.
  //
  // The semantics of the case operator is as follows.
  //
  // For each i = 0 to W - 1, where W is the width of the output/data:
  //
  // output.m_nId[output.m_nLsb + i] =
  //     if (bit_value(operands[0], i) == '1' then
  //         operands[1][operands[1].m_nLsb + i];
  //     else
  //     if (bit_value(operands[2], i) == '1' then
  //         operands[3][operands[3].m_nLsb + i];
  //     else
  //     if (bit_value(operands[4], i) == '1' then
  //         operands[5][operands[5].m_nLsb + i];
  //     ...
  //     else
  //     if (bit_value(operands[N - 2], i) == '1' then
  //         operands[N - 1][operands[N - 1].m_nLsb + i];
  //
  // Where bit_value(condition, index) is defined as follows:
  //
  // bit_value(IBitVector::BitRange condition, unsigned index) =
  //     if (condition.m_nLsb == condition.m_nMsb) then
  //         condition.m_nLsb;
  //     else
  //         condition.m_nLsb + index;
  //
  // I.e. if the condition is boolean, then the condition is the same for all
  // bits of the data. If the condition is of width of the output/data, then
  // each bit of the condition controls the corresponding bit of the data.
  //
  // There is a requirement that, for each bit of the output, at least one of
  // the conditions evaluates to '1' at any given time (the case is "full").
  //
  // The last condition is allowed to have a special value, representing the
  // "default" condition (the condition that is always "taken"). The default
  // condition is marked by the ID with value 0. The values of MSB/LSB of the
  // default condition are not required to have any pre-defined value.
  //
  // Arguments
  //
  // output - output of the operation
  // operands - operands of the operation
  //
  // Preconditions
  //
  // 1. All referenced data entities should be previously declared.
  // 2. Widths of ranges of all referenced data entities except
  //    operands with even indexes should be the same. The widths of
  //    referenced ranges of operands with even indexes should be either 1 or
  //    be the same as the widths of other referenced data entities.
  virtual void addCase (IBitVector::BitRange output,
                        const vector<BitRange>& operands)
  {
    assert (false);
  }

  // Method addParallelCase
  //
  // Adds a parallel case operator
  //
  // The parallel case operator is the same as the case operator, with the
  // additional requirement that, for each bit of the output, exactly one
  // condition should evaluate to '1' at the same time. See description of
  // the case operator (addCase() function) for more information.
  virtual void addParallelCase (IBitVector::BitRange output,
                                const vector<BitRange>& operands)
  {
    assert (false);
  }

  // Method addZeroExtension
  //
  // Zero extend a bit vector
  //
  // output = {{count{0}}, input}
  //
  // where count = (output.m_nMsb - output.m_nLsb) -
  //               (operand.m_nMsb - operand.m_nLsb)
  //
  // Arguments
  //
  // output - output of the operation
  // operand - operand of the operation
  //
  // Preconditions
  //
  // 1. The two referenced data entities should be previously declared.
  // 2. The width of operand should be less than width of output.
  virtual void addZeroExtension (IBitVector::BitRange output,
                                 IBitVector::BitRange operand)
  {
    assert (false);
  }

  // Method addSignExtension
  //
  // Sign extend a bit vector
  //
  // output = {{count{input[input.m_nMsb]}}, input}
  //
  // where count = (output.m_nMsb - output.m_nLsb) -
  //               (operand.m_nMsb - operand.m_nLsb)
  //
  // Arguments
  //
  // output - output of the operation
  // operand - operand of the operation
  //
  // Preconditions
  //
  // 1. The two referenced data entities should be previously declared.
  // 2. The width of operand should be less than width of output.
  virtual void addSignExtension (IBitVector::BitRange output,
                                 IBitVector::BitRange operand)
  {
    assert (false);
  }

  // Method addAssumption
  //
  // Adds an assumption that a particular bit of the given bit vector is 1
  //
  // Arguments
  //
  // bit - variable to be treated as assumption
  //
  // bIsInitial - boolean specifying whether the assumption is valid only in
  //     the initial state of the model, i.e. before any state transition
  //     takes place.
  //
  //     The value of this argument may be ignored if a combinational
  //     (vs. sequential) BitVector model is created.
  //
  // Preconditions
  //
  // 1. The referenced data entity should be previously declared.
  // 2. The width of the range of the referenced data entity should be 1.
  virtual void addAssumption (IBitVector::BitRange bit, bool bIsInitial = false)
  {
    assert (false);
  }

  // Method addFairnessConstraint
  //
  // Given a reference to a bit representing a liveness assertion and a
  // reference to a bit of another variable, specifies that the bit of
  // the other variable is a fairness constraint of the liveness assertion.
  //
  // Arguments
  //
  // livenessAssertion - reference to a bit representing a liveness assertion
  //
  // fairnessConstraint - reference to a bit representing a fairness
  //     constraint of the given liveness assertion
  //
  // Preconditions
  //
  // 1. The two referenced data entities should be previously declared.
  // 2. The width of the range of the two referenced data entities should
  //    be 1.
  // 3. livenessAssertion should be previously declared using addAssertion().
  virtual void addFairnessConstraint (IBitVector::BitRange livenessAssertion,
                                      IBitVector::BitRange fairnessConstraint)
  {
    assert (false);
  }

  // Method addAssertion
  //
  // Adds an assertion that a particular bit of the given bit vector
  // should be 1
  //
  // Arguments
  //
  // bit - variable to be treated as assertion
  //
  // Preconditions
  //
  // 1. The referenced data entity should be previously declared.
  // 2. The width of the range of the referenced data entity should be 1.
  virtual void addAssertion (IBitVector::BitRange bit) { assert (false); }

  // Method addMemory
  //
  // Declares a two-dimensional memory variable
  //
  // Arguments
  //
  // nId - ID of the memory
  // strName - name of the memory
  // nRowMsb - MSB of the memory rows (the address space)
  // nRowLsb - LSB of the memory rows (the address space)
  // nBitMsb - MSB of the memory bits (the data at each address)
  // nBitLsb - LSB of the memory bits (the data at each address)
  //
  // initialValue - optional initial value of the memory (value at clock
  //      tick 0). An empty vector represents an absence of the initial
  //      value. If the vector is not empty, its size should match the
  //      number of memory rows. The size of each string within the vector
  //      should match the number of memory bits. Each character of the
  //      string represents the initial value of the corresponding memory
  //      bit. The first character of the string denotes the MSB and the
  //      last character denotes the LSB. The allowed values are '0', '1'
  //      and 'u'. 'u' denotes an absence of the initial value at the
  //      particular bit ('unknown' value).
  //
  // Preconditions
  //
  // 1. No other declaration with the same ID should be previously made.
  // 2. nRowMsb should be greater than or equal to nRowLsb.
  // 3. nBitMsb should be greater than or equal to nBitLsb.
  virtual void addMemory (
      unsigned nId,
      const string& strName,
      unsigned nRowMsb,
      unsigned nRowLsb,
      unsigned nBitMsb,
      unsigned nBitLsb,
      const vector<string>& initialValue = vector<string> ())
  {
    assert (false);
  }

  // Method addMemoryRead
  //
  // Adds a memory read operation
  //
  // output = nMemoryId[rowSelection][nBitMsb:nBitLsb];
  //
  // Arguments
  //
  // nMemoryId - ID of the memory to read
  //
  // rowSelection - variable whose value specifies the memory row (address)
  //    to read
  //
  // nBitMsb - MSB of columns within the memory row to read
  // nBitLsb - LSB of columns within the memory row to read
  // output - output of the operation
  //
  // Preconditions
  //
  // 1. All the referenced data entities should be previously declared.
  // 2. nMemoryId should be declared using addMemory().
  // 3. The width of referenced range of output should be
  //    (nBitMsb - nBitLsb + 1).
  virtual void addMemoryRead (unsigned nMemoryId,
                              IBitVector::BitRange rowSelection,
                              unsigned nBitMsb,
                              unsigned nBitLsb,
                              IBitVector::BitRange output)
  {
    assert (false);
  }

  // Method addMemoryWrite
  //
  // Adds a memory write operation writing to a single memory row
  //
  // if (enableId)
  //     nMemoryOutId = memory_write(
  //          nMemoryInId[rowSelection][nBitMsb:nBitLsb],
  //          input);
  //
  // Arguments
  //
  // nMemoryOutId - ID of the memory representing the result of the memory
  //     write operation
  //
  // nMemoryInId - ID of the memory to which the memory write operation is
  //     applied
  //
  // rowSelection - variable whose value specifies the memory row (address)
  //     to write
  //
  // nBitMsb - MSB of columns within the memory row to write
  //
  // nBitLsb - LSB of columns within the memory row to write
  //
  // input - variable that holds the data that should be written into
  //     the memory
  //
  // enable - variable that enables the write operation
  //
  // Preconditions
  //
  // 1. All the referenced data entities should be previously declared.
  // 2. nMemoryOutId and nMemoryInId should be declared using addMemory().
  // 3. The width of the referenced range of input should be
  //    (bitMsb - bitLsb + 1).
  // 4. The width of the referenced range of enable should be 1.
  virtual void addMemoryWrite (unsigned nMemoryOutId,
                               unsigned nMemoryInId,
                               IBitVector::BitRange rowSelection,
                               unsigned nBitMsb,
                               unsigned nBitLsb,
                               IBitVector::BitRange input,
                               IBitVector::BitRange enable)
  {
    assert (false);
  }

  // Method addMemoryConstantWrite
  //
  // Adds a memory write operation writing to a range of memory rows with
  // known indexes. All selected memory rows are written the same value.
  //
  // if (enableId)
  //     nMemoryOutId = memory_write(
  //          nMemoryInId[nRowMsb:nRowLsb][nBitMsb:nBitLsb],
  //          input);
  //
  // Arguments
  //
  // nMemoryOutId - ID of the memory representing the result of the memory
  //     write operation
  //
  // nMemoryInId - ID of the memory to which the memory write operation is
  //     applied
  //
  // nRowMsb - MSB of the memory row to write
  //
  // nRowLsb - LSB of the memory row to write
  //
  // nBitMsb - MSB of columns within the memory row to write
  //
  // nBitLsb - LSB of columns within the memory row to write
  //
  // input - variable that holds the data that should be written into each
  //     selected memory row. The width of the data is the same as the width
  //     of the [nBitMsb:nBitLsb] range. The data is written to each memory
  //     row selected by the [nRowMsb:nRowLsb] range.
  //
  // enable - variable that enables the write operation
  //
  // Preconditions
  //
  // 1. All the referenced data entities should be previously declared.
  // 2. nMemoryOutId and nMemoryInId should be declared using addMemory().
  // 3. The width of the referenced range of input should be
  //    (bitMsb - bitLsb + 1).
  // 4. The width of the referenced range of enable should be 1.
  virtual void addMemoryConstantWrite (unsigned nMemoryOutId,
                                       unsigned nMemoryInId,
                                       unsigned nRowMsb,
                                       unsigned nRowLsb,
                                       unsigned nBitMsb,
                                       unsigned nBitLsb,
                                       IBitVector::BitRange input,
                                       IBitVector::BitRange enable)
  {
    assert (false);
  }

  // Method addMemoryEqual
  //
  // Adds a memory equality operation
  //
  // output = (nFirstMemoryId[nFirstMemoryRowMsb:nFirstMemoryRowLsb][
  //     nFirstMemoryBitMsb:nFirstMemoryBitLsb] ==
  //           nSecondMemoryId[nSecondMemoryRowMsb:nSecondMemoryRowLsb][
  //     nSecondMemoryBitMsb:nSecondMemoryBitLsb])
  //
  // If the bIsNegated argument is true, the operation checks whether
  // one memory is a negation of another, i.e. all bits of one memory that
  // have values 0, have values 1 in the other memory, and vice versa. If
  // bIsNegated is true, the semantics of the operation is:
  //
  // output = (nFirstMemoryId[nFirstMemoryRowMsb:nFirstMemoryRowLsb][
  //     nFirstMemoryBitMsb:nFirstMemoryBitLsb] ==
  //           not nSecondMemoryId[nSecondMemoryRowMsb:nSecondMemoryRowLsb][
  //     nSecondMemoryBitMsb:nSecondMemoryBitLsb])
  //
  // Arguments
  //
  // output - output of the operation
  // nFirstMemoryId - ID of the first memory to compare
  // nFirstMemoryRowMsb - MSB of the row range of the first memory
  // nFirstMemoryRowLsb - LSB of the row range of the first memory
  // nFirstMemoryBitMsb - MSB of the bit range of the first memory
  // nFirstMemoryBitLsb - LSB of the bit range of the first memory
  // nSecondMemoryId - ID of the second memory to compare
  // nSecondMemoryRowMsb - MSB of the row range of the second memory
  // nSecondMemoryRowLsb - LSB of the row range of the second memory
  // nSecondMemoryBitMsb - MSB of the bit range of the second memory
  // nSecondMemoryBitLsb - LSB of the bit range of the second memory
  //
  // bIsNegated - specifies whether the equality has the negated
  //     semantics, as described above
  //
  // Preconditions
  //
  // 1. All referenced data entities should be previously declared.
  // 2. The width of the referenced range of output should be 1.
  // 3. The total number of referenced bits of the two memories should be the
  //    same.
  virtual void addMemoryEqual (IBitVector::BitRange output,
                               unsigned nFirstMemoryId,
                               unsigned nFirstMemoryRowMsb,
                               unsigned nFirstMemoryRowLsb,
                               unsigned nFirstMemoryBitMsb,
                               unsigned nFirstMemoryBitLsb,
                               unsigned nSecondMemoryId,
                               unsigned nSecondMemoryRowMsb,
                               unsigned nSecondMemoryRowLsb,
                               unsigned nSecondMemoryBitMsb,
                               unsigned nSecondMemoryBitLsb,
                               bool bIsNegated)
  {
    assert (false);
  }

#endif
