#ifndef BTORIBV_H_INCLUDED
#define BTORIBV_H_INCLUDED

#include "IBitVector.h"

extern "C" {
#include "btorexp.h"
#include "btormc.h"
#include "btorstack.h"
};

class BtorIBV : public IBitVector
{
  Btor *btor;
  BtorNodePtrStack id2node;
  void addBtorNode (unsigned, BtorNode *);

 public:
  BtorIBV (Btor *);
  ~BtorIBV ();
  void addVariable (
      unsigned, const string &, unsigned, bool, bool, bool, DirectionKind);
#if 0
  void addState (BitRange, BitRange);
  void addConstant (unsigned, const string &, unsigned);
  void addBitOr (BitRange, BitRange, BitRange);
  void addBitAnd (BitRange, BitRange, BitRange);
  void addBitXor (BitRange, BitRange, BitRange);
  void addBitNot (BitRange, BitRange);
  void addConcat (BitRange output, const vector<BitRange>& operands);
  void addReplicate (BitRange output, BitRange operand, unsigned);
  void addEqual (BitRange, BitRange, BitRange);
  void addGreaterThan (BitRange, BitRange, BitRange);
  void addGreaterEqual (BitRange, BitRange, BitRange);
  void addLessThan (BitRange, BitRange, BitRange);
  void addLessEqual (BitRange, BitRange, BitRange);
  void addLogicalAnd (BitRange, BitRange, BitRange);
  void addLogicalOr (BitRange, BitRange, BitRange);
  void addLogicalNot (BitRange, BitRange, BitRange);
  void addSum (BitRange, BitRange, BitRange);
  void addSub (BitRange, BitRange, BitRange);
  void addMul (BitRange, BitRange, BitRange);
  void addDiv (BitRange, BitRange, BitRange);
  void addMod (BitRange, BitRange, BitRange);
  void addLShift (BitRange, BitRange, unsigned);
  void addRShift (BitRange, BitRange, unsigned);
  void addLShiftNonConst (BitRange, BitRange, BitRange);
  void addRShiftNonConst (BitRange, BitRange, BitRange);
  void addCondition (BitRange, BitRange, BitRange, BitRange);
  void addCase (BitRange, const vector<BitRange>&);
  void addParallelCase (BitRange, const vector<BitRange>&);
  void addZeroExtension (BitRange, BitRange);
  void addSignExtension (BitRange, BitRange);
  void addAssumption (BitRange, bool);
  void addFairnessConstraint (BitRange, BitRange);
  void addAssertion (BitRange);
  void addMemory (unsigned, const string&,
                  unsigned, unsigned,  unsigned, unsigned,
                  const vector<string>&);
  void addMemoryRead (unsigned, BitRange, unsigned, unsigned, BitRange);
  void addMemoryWrite (unsigned, unsigned, BitRange,
                       unsigned, unsigned, BitRange, BitRange);
  void addMemoryConstantWrite (unsigned, unsigned, unsigned, unsigned,
                               unsigned, unsigned, BitRange, BitRange);
  void addMemoryEqual (BitRange output,
		       unsigned, unsigned, unsigned, unsigned,
		       unsigned, unsigned, unsigned, unsigned,
		       unsigned, unsigned, bool);
#endif
};

#endif
