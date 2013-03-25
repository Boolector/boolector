#ifndef BTORIBV_H_INCLUDED
#define BTORIBV_H_INCLUDED

#include "IBitVector.h"

extern "C" {
#include "btorexp.h"
#include "btormc.h"
#include "btorstack.h"
};

// We use classical C style data structure in order to use the Boolector
// memory manager which is hard to use for C++ allocators ('new' and
// 'delete').  This needs explicit 'tags'.

enum BtorIBVTag
{

  BTOR_IBV_IS_UNARY    = 0,
  BTOR_IBV_NOT         = 0 + 0,
  BTOR_IBV_ZERO_EXTEND = 0 + 1,
  BTOR_IBV_SIGN_EXTEND = 0 + 2,

  BTOR_IBV_IS_BINARY = 16,
  BTOR_IBV_OR        = 16 + 0,
  BTOR_IBV_AND       = 16 + 1,
  BTOR_IBV_XOR       = 16 + 2,
  BTOR_IBV_LT        = 16 + 3,
  BTOR_IBV_LE        = 16 + 4,
  BTOR_IBV_SUM       = 16 + 5,
  BTOR_IBV_MUL       = 16 + 6,
  BTOR_IBV_DIV       = 16 + 7,
  BTOR_IBV_MOD       = 16 + 8,

  BTOR_IBV_IS_TERNARY = 32,
  BTOR_IBV_COND       = 32 + 0,

  BTOR_IBV_IS_VARIADIC = 64,

  BTOR_IBV_IS_PREDICATE = 128,
  BTOR_IBV_HAS_ARG      = 256,

  BTOR_IBV_MASK  = 15,
  BTOR_IBV_FLAGS = 16 | 32 | 64 | 128 | 256,
};

struct BtorIBVRange
{
  unsigned id, msb, lsb;
};

struct BtorIBVAssignment
{
  BtorIBVTag tag;
  unsigned msb, lsb;
  union
  {
    unsigned arg;      // if 'tag & BTOR_IBV_HAS_ARG'
    unsigned nranges;  // if 'tag & BTOR_IBV_IS_VARIADIC'
  };
  BtorIBVRange *ranges;  // size determined by 'tag' or 'nranges'
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

struct BtorIBVNode
{
  unsigned width : 31;
  unsigned is_constant : 1;
  unsigned id;
  BtorNode *cached;
  // Note: start of data for variables (invalid if 'is_constant')
  char *name;
  bool is_next_state;
  bool is_loop_breaking;
  bool is_state_retain;
  IBitVector::DirectionKind direction;
  BtorIBVAssignmentStack assignments;
  BtorIBVRangeNameStack ranges;
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

  BtorIBVNode *bitrange2node (BitRange range)
  {
    assert (range.m_nLsb <= range.m_nMsb);
    BtorIBVNode *node = id2node (range.m_nId);
    assert (node->width <= range.getWidth ());
    assert (range.m_nMsb < node->width);
    return node;
  }

  void delete_ibv_variable (BtorIBVNode *);
  void delete_ibv_constant (BtorIBVNode *);
  void delete_ibv_node (BtorIBVNode *);

  BtorIBVNode *new_node (unsigned id, bool isConstant, unsigned width);

  typedef BtorNode *(*BtorIBVBinOp) (Btor *, BtorNode *, BtorNode *);

  void addBinOp (BitRange, BitRange, BitRange, BtorIBVBinOp);
  void addBinPred (BitRange, BitRange, BitRange, BtorIBVBinOp);

  void wrn (const char *fmt, ...);
  void msg (int level, const char *fmt, ...);

 public:
  int verbosity;

  BtorIBV (Btor *);
  ~BtorIBV ();
  void addConstant (unsigned, const string &, unsigned);
  void addVariable (
      unsigned, const string &, unsigned, bool, bool, bool, DirectionKind);
  void addRangeName (BitRange, const string &, unsigned, unsigned);
#if 0
  void addState (BitRange, BitRange);
#endif

  void addBitOr (BitRange o, BitRange a, BitRange b)
  {
    addBinOp (o, a, b, btor_or_exp);
  }

  void addBitAnd (BitRange o, BitRange a, BitRange b)
  {
    addBinOp (o, a, b, btor_and_exp);
  }

  void addBitXor (BitRange o, BitRange a, BitRange b)
  {
    addBinOp (o, a, b, btor_xor_exp);
  }

  void addBitNot (BitRange, BitRange);
  void addConcat (BitRange output, const vector<BitRange> &operands);
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
  void addCase (BitRange, const vector<BitRange> &);
  void addParallelCase (BitRange, const vector<BitRange> &);
  void addZeroExtension (BitRange, BitRange);
  void addSignExtension (BitRange, BitRange);

#if 0
  void addAssumption (BitRange, bool);
  void addFairnessConstraint (BitRange, BitRange);
  void addAssertion (BitRange);
#endif

#if 0
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
