#ifndef BTORIBV_H_INCLUDED
#define BTORIBV_H_INCLUDED

#include "IBitVector.h"

extern "C" {
#include "btorexp.h"
#include "btormc.h"
#include "btorstack.h"
};

// We use classical C style data structures in order to be able to use the
// Boolector memory manager which is hard to use for C++ allocators ('new'
// and 'delete').  This needs explicit 'tags' and 'unions'.

enum BtorIBVTag
{

  BTOR_IBV_IS_UNARY    = 0,
  BTOR_IBV_NOT         = 0 + 0,
  BTOR_IBV_ZERO_EXTEND = 0 + 1,
  BTOR_IBV_SIGN_EXTEND = 0 + 2,
  BTOR_IBV_REPLICATE   = 0 + 3,
  BTOR_IBV_MAX_UNARY   = BTOR_IBV_REPLICATE,

  BTOR_IBV_IS_BINARY   = 16,
  BTOR_IBV_OR          = 16 + 0,
  BTOR_IBV_AND         = 16 + 1,
  BTOR_IBV_XOR         = 16 + 2,
  BTOR_IBV_LT          = 16 + 3,
  BTOR_IBV_LE          = 16 + 4,
  BTOR_IBV_SUM         = 16 + 5,
  BTOR_IBV_SUB         = 16 + 6,
  BTOR_IBV_MUL         = 16 + 7,
  BTOR_IBV_DIV         = 16 + 8,
  BTOR_IBV_MOD         = 16 + 9,
  BTOR_IBV_LEFT_SHIFT  = 16 + 10,
  BTOR_IBV_RIGHT_SHIFT = 16 + 11,
  BTOR_IBV_EQUAL       = 16 + 12,
  BTOR_IBV_MAX_BINARY  = BTOR_IBV_EQUAL,

  BTOR_IBV_IS_TERNARY  = 32,
  BTOR_IBV_COND        = 32 + 0,
  BTOR_IBV_MAX_TERNARY = BTOR_IBV_COND,

  BTOR_IBV_IS_VARIADIC  = 64,
  BTOR_IBV_CONCAT       = 64 + 0,
  BTOR_IBV_CASE         = 64 + 1,
  BTOR_IBV_PARCASE      = 64 + 2,
  BTOR_IBV_MAX_VARIADIX = BTOR_IBV_PARCASE,

  BTOR_IBV_IS_PREDICATE = 128,
  BTOR_IBV_HAS_ARG      = 256,
  BTOR_IBV_BITWISE      = 512,

  BTOR_IBV_OPS   = 15,
  BTOR_IBV_FLAGS = 16 | 32 | 64 | 128 | 256 | 512,
};

struct BtorIBVRange;

struct BtorIBVAssignment
{
  BtorIBVTag tag;
  unsigned msb, lsb, arg, nranges;
  BtorIBVRange *ranges;

  BtorIBVAssignment (BtorIBVTag t,
                     unsigned m,
                     unsigned l,
                     unsigned a,
                     unsigned n      = 0,
                     BtorIBVRange *r = 0)
      : tag (t), msb (m), lsb (l), arg (a), nranges (n), ranges (r)
  {
  }
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
  signed char *assigned, *marked;
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

  //------------------------------------------------------------------------

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

  void check_bit_range (BitRange range) { (void) bitrange2node (range); }

  BtorIBVNode *new_node (unsigned id, bool isConstant, unsigned width);

  void mark_assigned (BtorIBVNode *, BitRange);

  void delete_ibv_variable (BtorIBVNode *);
  void delete_ibv_constant (BtorIBVNode *);
  void delete_ibv_node (BtorIBVNode *);

  //------------------------------------------------------------------------

  void addUnary (BtorIBVTag, BitRange, BitRange);

  void addUnaryOp (BtorIBVTag tag, BitRange o, BitRange a)
  {
    assert (tag & BTOR_IBV_IS_UNARY);
    assert (tag <= BTOR_IBV_MAX_UNARY);
    addUnary (tag, o, a);
  }

  void addUnaryArg (BtorIBVTag, BitRange, BitRange, unsigned);

  void addUnaryPred (BtorIBVTag tag, BitRange o, BitRange a)
  {
    assert (tag & BTOR_IBV_IS_UNARY);
    assert (tag <= BTOR_IBV_MAX_UNARY);
    addUnary ((BtorIBVTag) (tag | BTOR_IBV_IS_PREDICATE), o, a);
  }

  //------------------------------------------------------------------------

  void addBinary (BtorIBVTag, BitRange, BitRange, BitRange);

  void addBinaryOp (BtorIBVTag tag, BitRange o, BitRange a, BitRange b)
  {
    assert (tag & BTOR_IBV_IS_BINARY);
    assert (tag <= BTOR_IBV_MAX_BINARY);
    addBinary (tag, o, a, b);
  }

  void addBinaryPred (BtorIBVTag tag, BitRange o, BitRange a, BitRange b)
  {
    assert (tag & BTOR_IBV_IS_BINARY);
    assert (tag <= BTOR_IBV_MAX_BINARY);
    addBinary ((BtorIBVTag) (tag | BTOR_IBV_IS_PREDICATE), o, a, b);
  }

  //------------------------------------------------------------------------

  void wrn (const char *fmt, ...);
  void msg (int level, const char *fmt, ...);

 public:
  int verbosity;

  BtorIBV (Btor *);
  ~BtorIBV ();

  //------------------------------------------------------------------------

  void addConstant (unsigned, const string &, unsigned);
  void addVariable (
      unsigned, const string &, unsigned, bool, bool, bool, DirectionKind);

  void addRangeName (BitRange, const string &, unsigned, unsigned);

  //------------------------------------------------------------------------

#if 0
  void addState (BitRange, BitRange);
  void addNonState (BitRange, BitRange);
#endif

  //------------------------------------------------------------------------

  void addBitNot (BitRange o, BitRange a) { addUnaryOp (BTOR_IBV_NOT, o, a); }
  void addZeroExtension (BitRange o, BitRange a)
  {
    addUnaryOp (BTOR_IBV_ZERO_EXTEND, o, a);
  }
  void addSignExtension (BitRange o, BitRange a)
  {
    addUnaryOp (BTOR_IBV_SIGN_EXTEND, o, a);
  }
  void addLogicalNot (BitRange o, BitRange a)
  {
    addUnaryPred (BTOR_IBV_NOT, o, a);
  }

  //------------------------------------------------------------------------

  void addBitOr (BitRange o, BitRange a, BitRange b)
  {
    addBinaryOp (BTOR_IBV_OR, o, a, b);
  }
  void addBitAnd (BitRange o, BitRange a, BitRange b)
  {
    addBinaryOp (BTOR_IBV_AND, o, a, b);
  }
  void addBitXor (BitRange o, BitRange a, BitRange b)
  {
    addBinaryOp (BTOR_IBV_XOR, o, a, b);
  }
  void addEqual (BitRange o, BitRange a, BitRange b)
  {
    addBinaryPred (BTOR_IBV_EQUAL, o, a, b);
  }
  void addGreaterThan (BitRange o, BitRange a, BitRange b)
  {
    addBinaryPred (BTOR_IBV_LT, o, b, a);
  }
  void addGreaterEqual (BitRange o, BitRange a, BitRange b)
  {
    addBinaryPred (BTOR_IBV_LE, o, b, a);
  }
  void addLessThan (BitRange o, BitRange a, BitRange b)
  {
    addBinaryPred (BTOR_IBV_LT, o, a, b);
  }
  void addLessEqual (BitRange o, BitRange a, BitRange b)
  {
    addBinaryPred (BTOR_IBV_LE, o, a, b);
  }
  void addLogicalAnd (BitRange o, BitRange a, BitRange b)
  {
    addBinaryPred (BTOR_IBV_AND, o, a, b);
  }
  void addLogicalOr (BitRange o, BitRange a, BitRange b)
  {
    addBinaryPred (BTOR_IBV_OR, o, a, b);
  }
  void addSum (BitRange o, BitRange a, BitRange b)
  {
    addBinaryOp (BTOR_IBV_SUM, o, a, b);
  }
  void addSub (BitRange o, BitRange a, BitRange b)
  {
    addBinaryOp (BTOR_IBV_SUB, o, a, b);
  }
  void addMul (BitRange o, BitRange a, BitRange b)
  {
    addBinaryOp (BTOR_IBV_MUL, o, a, b);
  }
  void addDiv (BitRange o, BitRange a, BitRange b)
  {
    addBinaryOp (BTOR_IBV_DIV, o, a, b);
  }
  void addMod (BitRange o, BitRange a, BitRange b)
  {
    addBinaryOp (BTOR_IBV_MOD, o, a, b);
  }
  void addLShiftNonConst (BitRange o, BitRange a, BitRange b)
  {
    addBinaryOp (BTOR_IBV_LEFT_SHIFT, o, a, b);
  }
  void addRShiftNonConst (BitRange o, BitRange a, BitRange b)
  {
    addBinaryOp (BTOR_IBV_RIGHT_SHIFT, o, a, b);
  }

  //------------------------------------------------------------------------

  void addCondition (BitRange, BitRange, BitRange, BitRange);

  //------------------------------------------------------------------------

  void addReplicate (BitRange o, BitRange a, unsigned arg)
  {
    addUnaryArg (BTOR_IBV_REPLICATE, o, a, arg);
  }
  void addLShift (BitRange o, BitRange a, unsigned arg)
  {
    addUnaryArg (BTOR_IBV_LEFT_SHIFT, o, a, arg);
  }
  void addRShift (BitRange o, BitRange a, unsigned arg)
  {
    addUnaryArg (BTOR_IBV_RIGHT_SHIFT, o, a, arg);
  }

  //------------------------------------------------------------------------

  void addConcat (BitRange output, const vector<BitRange> &operands);
  void addCase (BitRange, const vector<BitRange> &);
  void addParallelCase (BitRange, const vector<BitRange> &);

#if 0

  //------------------------------------------------------------------------

  void addAssumption (BitRange, bool);
  void addFairnessConstraint (BitRange, BitRange);
  void addAssertion (BitRange);

  //------------------------------------------------------------------------

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

struct BtorIBVRange
{
  unsigned id, msb, lsb;
  BtorIBVRange (unsigned i, unsigned m, unsigned l) : id (i), msb (m), lsb (l)
  {
  }
  BtorIBVRange (const IBitVector::BitRange &r)
      : id (r.m_nId), msb (r.m_nMsb), lsb (r.m_nLsb)
  {
  }
};

#endif
