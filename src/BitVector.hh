/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2012-2013 Armin Biere.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BitVector_h_INCLUDED
#define BitVector_h_INCLUDED

#include <cassert>
#include <functional>
#include <string>
#include <vector>

using namespace std;

// This class defines an industrially used BitVector API interface.

class BitVector
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

  // Specifies the direction of a variable, for flows that use hierarchical
  // BitVector models
  typedef enum
  {
    INTERNAL,
    INPUT,
    OUTPUT,
    INOUT
  } DirectionKind;

  typedef enum
  {
    MODULE,
    TYPEDEF,
    PARAMETER,
    PROPERTY_TEMPLATE,
    FUNCTION,
    PACKAGE,
    PACKAGE_IMPORT,
    INTERFACE
  } SourceConstructKind;

  typedef enum
  {
    TRI,
    RTRI,
    NTRI,
    RNTRI,
    WAND_WEAKPULL,
    WAND_DISCHARGE,
    WOR_WEAKPULL,
    WOR_DISCHARGE,
    PP_PRECHARGE,
    PP_DISCHARGE,
    NP_PRECHARGE,
    NP_DISCHARGE
  } BusDriverKind;

  // Specifies the source of the variable
  typedef enum
  {
    // No specific information about the source of the variable is available
    NONE,

    // Specifies that the variable represents an output of a past operator
    // modeling retain value of a state signal
    STATE_RETAIN,

    // Specifies that the variable represents an intermediate result of an
    // operator and not a signal (e.g. EXP_17 represents an intermediate
    // result of a+b in expression (a+b)+c).
    INTERMEDIATE_RESULT,

    // Specifies that the variable represents a variable created by More
    // during applying loop breaking algorithm
    LOOP_BREAKER,

    // Specifies that the variable represents an output of a $past()
    // operator other than operators whose output is represented with
    // STATE_RETAIN, CLOCK_PAST CLOCK_TMP_PAST variables
    PAST,

    // Specifies that the variable represents a clock signal
    CLOCK,

    // Specifies that the variable represents an output of a $past()
    // operator applied on a clock signal
    CLOCK_PAST,

    // Specifies that the variable represents a temporary variable created
    // by More during clock toggling modeling
    CLOCK_TMP,

    // Specifies that the variable represents an output of a $past()
    // operator applied on a temporary variable created by More during clock
    // toggling modeling
    CLOCK_TMP_PAST,

    // Specifies that the variable represents a variable created by More
    // during creation of dummy assumption
    DUMMY_ASSUMPTION
  } BvVariableSource;

 public:
  // Method ~BitVector
  //
  // Destructor
  //
  // declared only since it must be virtual
  virtual ~BitVector (){};

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wunused-parameter"

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
                            bool bIsNextStateVariable   = false,
                            BitVector::BvVariableSource = NONE,

                            BitVector::DirectionKind eDirection = INTERNAL)
  {
    assert (false);
  }

  //
  // OLD DEPRECATED 7 ARGUMENT VERSION.
  //
  void addVariableOld (unsigned nId,
                       const string& strName,
                       unsigned nWidth,
                       bool bIsNextStateVariable           = false,
                       bool bIsLoopBreakingVariable        = false,
                       bool bIsStateRetainVariable         = false,
                       BitVector::DirectionKind eDirection = INTERNAL)
  {
    addVariable (nId, strName, nWidth, bIsNextStateVariable, NONE, eDirection);
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
  virtual void addRangeName (BitVector::BitRange bitRange,
                             const string& strRangeName,
                             unsigned nRangeMsb,
                             unsigned nRangeLsb)
  {
    // The default implementation is empty, as to not require all
    // implementations of BitVector to implement this method
  }

  virtual void addRangeDirection (BitVector::BitRange bitRange,
                                  BitVector::DirectionKind eDirection)
  {
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
  virtual void addState (BitVector::BitRange variable,
                         BitVector::BitRange initValue,
                         BitVector::BitRange nextState)
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
  virtual void addNonState (BitVector::BitRange variable,
                            BitVector::BitRange nextState)
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
  virtual void addAssignment (BitVector::BitRange output,
                              BitVector::BitRange input)
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
  virtual void addBitOr (BitVector::BitRange output,
                         BitVector::BitRange firstOperand,
                         BitVector::BitRange secondOperand)
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
  virtual void addBitAnd (BitVector::BitRange output,
                          BitVector::BitRange firstOperand,
                          BitVector::BitRange secondOperand)
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
  virtual void addBitXor (BitVector::BitRange output,
                          BitVector::BitRange firstOperand,
                          BitVector::BitRange secondOperand)
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
  virtual void addBitNot (BitVector::BitRange output,
                          BitVector::BitRange operand)
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
  virtual void addConcat (BitVector::BitRange output,
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
  virtual void addReplicate (BitVector::BitRange output,
                             BitVector::BitRange operand,
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
  virtual void addEqual (BitVector::BitRange output,
                         BitVector::BitRange firstOperand,
                         BitVector::BitRange secondOperand)
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
  virtual void addGreaterThan (BitVector::BitRange output,
                               BitVector::BitRange firstOperand,
                               BitVector::BitRange secondOperand)
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
  virtual void addGreaterEqual (BitVector::BitRange output,
                                BitVector::BitRange firstOperand,
                                BitVector::BitRange secondOperand)
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
  virtual void addLessThan (BitVector::BitRange output,
                            BitVector::BitRange firstOperand,
                            BitVector::BitRange secondOperand)
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
  virtual void addLessEqual (BitVector::BitRange output,
                             BitVector::BitRange firstOperand,
                             BitVector::BitRange secondOperand)
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
  virtual void addLogicalAnd (BitVector::BitRange output,
                              BitVector::BitRange firstOperand,
                              BitVector::BitRange secondOperand)
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
  virtual void addLogicalOr (BitVector::BitRange output,
                             BitVector::BitRange firstOperand,
                             BitVector::BitRange secondOperand)
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
  virtual void addLogicalNot (BitVector::BitRange output,
                              BitVector::BitRange operand)
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
  virtual void addSum (BitVector::BitRange output,
                       BitVector::BitRange firstOperand,
                       BitVector::BitRange secondOperand)
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
  virtual void addSub (BitVector::BitRange output,
                       BitVector::BitRange firstOperand,
                       BitVector::BitRange secondOperand)
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
  virtual void addMul (BitVector::BitRange output,
                       BitVector::BitRange firstOperand,
                       BitVector::BitRange secondOperand)
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
  virtual void addDiv (BitVector::BitRange output,
                       BitVector::BitRange firstOperand,
                       BitVector::BitRange secondOperand)
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
  virtual void addMod (BitVector::BitRange output,
                       BitVector::BitRange firstOperand,
                       BitVector::BitRange secondOperand)
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
  virtual void addLShift (BitVector::BitRange output,
                          BitVector::BitRange operand,
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
  virtual void addRShift (BitVector::BitRange output,
                          BitVector::BitRange operand,
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
  virtual void addLShiftNonConst (BitVector::BitRange output,
                                  BitVector::BitRange operand,
                                  BitVector::BitRange shiftAmount)
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
  virtual void addRShiftNonConst (BitVector::BitRange output,
                                  BitVector::BitRange operand,
                                  BitVector::BitRange shiftAmount)
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
  virtual void addCondition (BitVector::BitRange output,
                             BitVector::BitRange conditionOperand,
                             BitVector::BitRange thenOperand,
                             BitVector::BitRange elseOperand)
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
  // bit_value(BitVector::BitRange condition, unsigned index) =
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
  virtual void addCase (BitVector::BitRange output,
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
  virtual void addParallelCase (BitVector::BitRange output,
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
  virtual void addZeroExtension (BitVector::BitRange output,
                                 BitVector::BitRange operand)
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
  virtual void addSignExtension (BitVector::BitRange output,
                                 BitVector::BitRange operand)
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
  virtual void addAssumption (BitVector::BitRange bit, bool bIsInitial = false)
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
  virtual void addFairnessConstraint (BitVector::BitRange livenessAssertion,
                                      BitVector::BitRange fairnessConstraint)
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
  virtual void addAssertion (BitVector::BitRange bit) { assert (false); }

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
                              BitVector::BitRange rowSelection,
                              unsigned nBitMsb,
                              unsigned nBitLsb,
                              BitVector::BitRange output)
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
                               BitVector::BitRange rowSelection,
                               unsigned nBitMsb,
                               unsigned nBitLsb,
                               BitVector::BitRange input,
                               BitVector::BitRange enable)
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
                                       BitVector::BitRange input,
                                       BitVector::BitRange enable)
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
  virtual void addMemoryEqual (BitVector::BitRange output,
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

  // Method addModuleBegin
  //
  // Notifies the BitVector implementation on the beginning of a declaration
  // of a new module. The call to addModuleBegin() should be followed by zero
  // or more calls to other BitVector methods and a call to addModuleEnd()
  // method. All BitVector calls between the addModuleBegin() call and the
  // following addModuleEnd() call define the contents of the module being
  // declared. Variables declared with addVariable() calls, whose direction is
  // not the INTERNAL direction, define the ports of the module.
  //
  // Arguments
  //
  // nModuleId - an unique ID of the new module
  // strModuleName - name of the module
  //
  // Preconditions
  //
  // 1. All preceding addModuleBegin() calls should be followed by the
  //    corresponding addModuleEnd() calls. There should be no nesting of
  //    addModuleBegin() calls.
  virtual void addModuleBegin (unsigned nModuleId,
                               const string& strModuleName,
                               const string& strTemplateModuleName,
                               const vector<string>& strParameters)
  {
    // The default implementation is empty, as to not require all
    // implementations of BitVector to implement this method
  }

  // Method addModuleEnd
  //
  // Notifies the BitVector implementation on the end of a declaration
  // of a new module. See addModuleBegin() documentation for more information.
  //
  // Preconditions
  //
  // 1. An addModuleBegin() call, not followed by a corresponding
  //    addModuleEnd() call, should be made before the call to this method.
  virtual void addModuleEnd ()
  {
    // The default implementation is empty, as to not require all
    // implementations of BitVector to implement this method
  }

  // Method addDesignBegin
  //
  // Notifies the BitVector implementation on the beginning of a declaration
  // of a new design. The call to addDesignBegin() should be followed by zero
  // or more calls to other BitVector methods and a call to addDesignEnd()
  // method. All BitVector calls between the addDesignBegin() call and the
  // following addDesignEnd() call define the contents of the design being
  // declared.
  //
  // Arguments
  //
  // nDesignId - an unique ID of the new design
  // strDesignName - name of the design
  //
  // Preconditions
  //
  // 1. All preceding addDesignBegin() calls should be followed by the
  //    corresponding addDesignEnd() calls. There should be no nesting of
  //    addDesignBegin() calls.
  virtual void addDesignBegin (unsigned nDesignId, const string& strDesignName)
  {
    // The default implementation is empty, as to not require all
    // implementations of BitVector to implement this method
  }

  // Method addDesignEnd
  //
  // Notifies the BitVector implementation on the end of a declaration
  // of a design. See addDesignBegin() documentation for more information.
  //
  // Preconditions
  //
  // 1. An addDesignBegin() call, not followed by a corresponding
  //    addDesignEnd() call, should be made before the call to this method.
  virtual void addDesignEnd ()
  {
    // The default implementation is empty, as to not require all
    // implementations of BitVector to implement this method
  }

  // Method addInstance
  //
  // Adds an instance of the given module
  //
  // Arguments
  //
  // nInstanceId - an unique ID of the new instance
  // strInstanceName - instance name: the name from instance_name attribute if
  //     exists or RTL instance name.
  // strOriginalInstanceName - RTL instance name
  // nModuleId - ID of the module to be instantiated
  // strModuleName - name of the module to be instantiated
  //
  // portConnections - pairs of references to data entities to be connected to
  //     the module's ports and corresponding port name.
  //
  // Preconditions
  //
  // 1. The module to be instantiated should be previously declared.
  // 2. All the referenced data entities in portConnections should be
  //    previously declared.
  // 3. The number of port connections should match the number of module's
  //    ports and the width of each port connection should match the width
  //    of the port it is connected to.
  virtual void addInstance (
      unsigned nInstanceId,
      const string& strInstanceName,
      const string& strOriginalInstanceName,
      unsigned nModuleId,
      const string& strModuleName,
      const vector<pair<BitVector::BitRange, string> >& portConnections)
  {
    // The default implementation is empty, as to not require all
    // implementations of BitVector to implement this method
  }

  // Method addHierarchyBegin
  //
  // Adds a declaration and an instance of a new module, creating a new
  // hierarchical entity grouping the given list of other hierarchical
  // entities.
  //
  // Arguments
  //
  // nHierarchyId - an unique ID of the new hierarchy
  // strHierarchyName - name of the hierarchy
  //
  // instances - instances of other hierarchical entities, to be placed within
  //    the module. Instances of other hierarchical entities can be one of
  //    the following two kinds:
  //
  //     1. Instances of other modules, created with either addInstance() or
  //        addHierarchy() functions. In this case, the instance is to be
  //        specified as a BitRange referring to the ID of the corresponding
  //        instance, with [0:0] used as the BitRange's range.
  //
  //     2. Any BitVector operator, created with one of the
  //        add<operator_name>() functions. In this case, the instance is to
  //        be specified as the BitRange representing the operator's output.
  //
  // bIsTopLevel - indicates whether the hierarchy is a top level hierarchy
  // (directed under a module).
  //
  //
  // Preconditions
  //
  // 1. All referenced instances should be previously declared.
  virtual void addHierarchyBegin (unsigned nHierarchyId,
                                  const string& strHierarchyName,
                                  const vector<BitVector::BitRange>& instances,
                                  bool bIsTopLevel)
  {
    // The default implementation is empty, as to not require all
    // implementations of BitVector to implement this method
  }

  // Notifies the BitVector implementation on the end of a declaration
  // of a new hierarchy. See addHierarchyBegin() documentation for more
  // information.
  //
  // Preconditions
  //
  // 1. An addHierarchyBegin() call, not followed by a corresponding
  //    addHierarchyEnd() call, should be made before the call to this method.
  virtual void addHierarchyEnd ()
  {
    // The default implementation is empty, as to not require all
    // implementations of BitVector to implement this method
  }

  // Method addSourceText
  //
  // Adds a source text on the given BitRange.
  //
  // Arguments
  //
  // bitRange -  BitRange to put the attribute on. The BitRange refers to
  //     one of the hierarchies
  // strSourceText - source text of the given hierarchy
  //
  // Preconditions
  //
  // 1. All referenced hierarchies should be previously declared.
  virtual void addSourceText (BitVector::BitRange bitRange,
                              const string& strSourceText)
  {
    // The default implementation is empty, as to not require all
    // implementations of BitVector to implement this method
  }

  // Method addSourceLocation
  //
  // Provides back annotation to the rtl.
  // Adds a source location on the given BitRange.
  //
  // Arguments
  //
  // bitRange -  BitRange to put the attribute on.
  // strFile - The file name from the source reference.
  // nFirstLine - The first line number for the source reference.
  // nLastLine - The last line number for the source reference.
  // nFirstColumn - The first column number for the source reference.
  // nLastColumn - The last column number for the source reference.
  //
  // Preconditions
  //
  // 1. All referenced hierarchies should be previously declared.
  virtual void addSourceLocation (BitVector::BitRange bitRange,
                                  const string& strFile,
                                  unsigned nFirstLine,
                                  unsigned nLastLine,
                                  unsigned nFirstColumn,
                                  unsigned nLastColumn)
  {
    // The default implementation is empty, as to not require all
    // implementations of BitVector to implement this method
  }

  // Method addSourceConstruct
  //
  // Adds an source construct.
  //
  // Arguments
  //
  // nId - an unique ID of the new source construct
  // strName - construct name
  // nModuleId - ID of the module to be instantiated
  // eConstructKind - sourcer construct kind. E.g. parameter, function, etc.

  //
  // Preconditions
  //
  // 1. All referenced constructs should be previously declared.
  virtual void addSourceConstruct (
      unsigned nId,
      const string& strName,
      BitVector::SourceConstructKind eConstructKind)
  {
    // The default implementation is empty, as to not require all
    // implementations of BitVector to implement this method
  }

  // Method addDependencies
  //
  // Adds dependencies of a given source construct.
  //
  // Arguments
  //
  // nConstructId - an unique ID of the new source construct
  // dependencies - vector of IDs of source constructs that a given source
  // contruct depends on them.

  //
  // Preconditions
  //
  // 1. All referenced constructs should be previously declared.
  virtual void addDependencies (unsigned nConstructId,
                                const vector<unsigned>& dependencies)
  {
    // The default implementation is empty, as to not require all
    // implementations of BitVector to implement this method
  }

  // Method addPort
  //
  // Adds port
  //
  // Arguments
  //
  // strPortName - a port name
  // bitBlastedPortNames - vector of bit blasted port names.

  //
  // Preconditions
  //
  // 1. All referenced constructs should be previously declared.
  virtual void addPort (const string& strPortName,
                        const vector<string>& bitBlastedPortNames)
  {
    // The default implementation is empty, as to not require all
    // implementations of BitVector to implement this method
  }

  // Method addLatch
  //
  // Adds an instance of a latch primitive
  //
  // Arguments
  //
  // nInstanceId - an unique ID of the new instance
  // strInstanceName - instance name
  // output - latch's output
  //
  // clock - latch's clock. The clock may be null, represented by ID equal to
  //     0. If the clock is null, the latch must have a non-null enable and
  //     null asyncSet and asyncReset. If the clock is null, bIsActiveHigh
  //     must be true.
  //
  // enable - latch's enable. Enable may be null, if latch's clock is
  //     non-null.
  //
  // input - latch's input. Input must have a non-null ID.
  //
  // asyncSet - latch's asynchronous set. Asynchronous set may be non-null
  //      only if latch's clock is non-null.
  //
  // asyncReset - latch's asynchronous reset. Asynchronous rest may be
  //      non-null only if latch's clock is non-null.
  //
  // bIsActiveHigh - specifies whether the latch is open at high (1) clock or
  //      low (0) clock. bIsActiveHigh may be false only if latch's clock is
  //      non-null.
  //
  // Preconditions
  //
  // 1. All the referenced data entities in should be previously declared.
  // 2. Width of ranges of clock, enable, asyncSet and asyncReset arguments
  //    should be 1.
  // 3. Width of ranges of output and input should be the same.
  virtual void addLatch (unsigned nInstanceId,
                         const string& strInstanceName,
                         BitVector::BitRange output,
                         BitVector::BitRange clock,
                         BitVector::BitRange enable,
                         BitVector::BitRange input,
                         BitVector::BitRange asyncSet,
                         BitVector::BitRange asyncReset,
                         bool bIsActiveHigh)
  {
    // The default implementation is empty, as to not require all
    // implementations of BitVector to implement this method
  }

  // Method addFlipFlop
  //
  // Adds an instance of a flip-flop primitive
  //
  // Arguments
  //
  // nInstanceId - an unique ID of the new instance
  // strInstanceName - instance name
  // output - flip-flop's output
  //
  // clock - flip-flop's clock. Must have a non-null ID.
  //
  // enable - flip-flop's enable. Must have a non-null ID.
  //
  // input - flip-flop's input. Input must have a non-null ID.
  //
  // asyncSet - flip-flop's asynchronous set. Asynchronous set may have a
  //     null ID.
  //
  // asyncReset - flip-flop's asynchronous reset. Asynchronous reset may have
  //     a null ID.
  //
  // bIsRising - specifies whether the flip-flop is open at rising edge of
  //     the clock or at falling edge.
  //
  // Preconditions
  //
  // 1. All the referenced data entities in should be previously declared.
  // 2. Width of ranges of clock and enable arguments should be 1.
  // 3. Width of ranges of output, input, asyncSet and asyncReset should be
  //    the same.
  virtual void addFlipFlop (unsigned nInstanceId,
                            const string& strInstanceName,
                            BitVector::BitRange output,
                            BitVector::BitRange clock,
                            BitVector::BitRange enable,
                            BitVector::BitRange input,
                            BitVector::BitRange asyncSet,
                            BitVector::BitRange asyncReset,
                            bool bIsRising)
  {
    // The default implementation is empty, as to not require all
    // implementations of BitVector to implement this method
  }

  // Method addBusDriver
  //
  // Adds an instance of a bus driver.
  //
  // Arguments
  //
  // nInstanceId - an unique ID of the new instance
  // strInstanceName - instance name
  // output - bus driver's output.
  // enable - bus driver's enable.
  // input - bus driver's input.
  // eBusDriverKind - bus driver's kind.
  //
  // Preconditions
  //
  // 1. All the referenced data entities in should be previously declared.
  // 2. Widths of ranges of the output and input should be the same.
  // 3. Width of ranges of enable arguments should be 1.
  virtual void addBusDriver (unsigned nInstanceId,
                             const string& strInstanceName,
                             BitVector::BitRange output,
                             BitVector::BitRange enable,
                             BitVector::BitRange input,
                             BitVector::BusDriverKind eBusDriverKind)
  {
    // The default implementation is empty, as to not require all
    // implementations of BitVector to implement this method
  }

  // Method addDelay
  //
  // Adds an instance of a delay primitive. Delay primitive behaves as a
  // flip-flop whose clock is always active (as if it would be connected to
  // the fastest clock in the system).
  //
  // Arguments
  //
  // nInstanceId - an unique ID of the new instance
  // strInstanceName - instance name
  // output - delay primitive's output
  // enable - delay primitive's enable. Enable may have a null ID.
  // input - delay primitive's input
  //
  // Preconditions
  //
  // 1. All the referenced data entities in should be previously declared.
  // 2. Widths of ranges of output and input should be the
  //    same.
  virtual void addDelay (unsigned nInstanceId,
                         const string& strInstanceName,
                         BitVector::BitRange output,
                         BitVector::BitRange enable,
                         BitVector::BitRange input)
  {
    // The default implementation is empty, as to not require all
    // implementations of BitVector to implement this method
  }

  // Method addAttribute
  //
  // Adds a new attribute on the given BitRange.
  //
  // Arguments
  //
  // bitRange - BitRange to put the attribute on. The BitRange may refer to
  //     one of the following entities:
  //
  //     1. A data entity declaration, declared using addVariable(),
  //        addConstant() or addMemory().
  //
  //     2. A module declaration, declared using addModuleBegin() or
  //        addHierarchyBegin().
  //
  //     3. An instance declaration, declared using addInstance() or
  //        addHierarchyBegin().
  //
  //     4. An operator declaration, declared using one of the
  //        add<operator_name>() functions.
  //
  //     For the first 3 entity kinds, the given BitRange should refer to ID
  //     of the entity, with [0:0] used as the BitRange's range. For the 4th
  //     entity kind, the BitRange should refer to the BitRange of the
  //     operator's output.
  //
  // strName - name of the attribute
  // strValue - value of the attribute
  //
  // Preconditions
  //
  // 1. The entity referenced by bitRange should be previously declared.
  virtual void addAttribute (BitVector::BitRange bitRange,
                             const string& strName,
                             const string& strValue)
  {
    // The default implementation is empty, as to not require all
    // implementations of BitVector to implement this method
  }

  // Method finalizeModelCreation
  //
  // This method is called at the end of model creation. Implementations
  // of BitVector interface may override this method to perform
  // implementation specific procedures finalizing model creation.
  virtual void finalizeModelCreation ()
  {
    // The default implementation is empty, as to not require all
    // implementations of BitVector to implement this method
  }
};

#pragma GCC diagnostic pop

#endif
