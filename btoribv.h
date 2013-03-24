#ifndef BTORIBV_H_INCLUDED
#define BTORIBV_H_INCLUDED

#include "IBitVector.h"

extern "C" {
#include "btorexp.h"
#include "btormc.h"
#include "btorstack.h"
};

enum BtorIBVTag
{
  BTOR_IBV_VARIABLE,
  BTOR_IBV_CONSTANT,
  BTOR_IBV_BVOP,
};

struct BtorIBVAssignment
{
  unsigned msb, lsb;
  BtorNode *rhs;
};

extern "C" {
BTOR_DECLARE_STACK (IBVAssignment, BtorIBVAssignment);
};

struct BtorIBVRangeName
{
  struct
  {
    unsigned msb, lsb;
  } from, to;
  char *name;
};

extern "C" {
BTOR_DECLARE_STACK (IBVRangeName, BtorIBVRangeName);
};

struct BtorIBVariable
{
  char *name;
  bool is_next_state;
  bool is_loop_breaking;
  bool is_state_retain;
  IBitVector::DirectionKind direction;
  BtorIBVAssignmentStack assignments;
  BtorIBVRangeNameStack ranges;
};

struct BtorIBVNode
{
  BtorIBVTag tag;
  unsigned id;
  unsigned width;
  BtorNode *exp;
  BtorIBVariable *var;
};

extern "C" {
BTOR_DECLARE_STACK (IBVNodePtr, BtorIBVNode *);
};

class BtorIBV : public IBitVector
{
  Btor *btor;
  BtorIBVNodePtrStack idtab;

  BtorIBVNode *id2node (unsigned id)
  {
    BtorIBVNode *node;
    assert (0 < id);
    node = BTOR_PEEK_STACK (idtab, id);
    assert (node);
    return node;
  }

  void delete_ibv_node (BtorIBVNode *);
  void delete_ibv_var (BtorIBVariable *);
  BtorIBVNode *new_node (unsigned, BtorIBVTag, unsigned, BtorNode *);

 public:
  BtorIBV (Btor *);
  ~BtorIBV ();
  void addConstant (unsigned, const string &, unsigned);
  void addVariable (
      unsigned, const string &, unsigned, bool, bool, bool, DirectionKind);
  void addRangeName (BitRange, const string &, unsigned, unsigned);
#if 0
  void addState (BitRange, BitRange);
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
