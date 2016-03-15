/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2015 Armin Biere.
 *  Copyright (C) 2012-2015 Aina Niemetz.
 *  Copyright (C) 2012-2015 Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTOREXP_H_INCLUDED
#define BTOREXP_H_INCLUDED

#include "btoraigvec.h"
#include "btorbitvec.h"
#include "btorsort.h"
#include "btortypes.h"
#include "utils/btorhashptr.h"
#include "utils/btorqueue.h"
#include "utils/btorstack.h"

/*------------------------------------------------------------------------*/

BTOR_DECLARE_STACK (BtorNodePtr, BtorNode *);
BTOR_DECLARE_STACK (BtorNodePtrPtr, BtorNode **);
BTOR_DECLARE_QUEUE (BtorNodePtr, BtorNode *);

/*------------------------------------------------------------------------*/

BTOR_DECLARE_STACK (BoolectorNodePtr, BoolectorNode *);

/*------------------------------------------------------------------------*/

/* NOTE: DO NOT REORDER THE INDICES.
 * CERTAIN MACROS DEPEND ON ORDER.
 * Some code also depends on that BTOR_INVALID_NODE, BTOR_CONST_NODE
 * and BTOR_VAR_NODE are at the beginning,
 * and BTOR_PROXY_NODE is BTOR_NUM_OPS_NODE - 1
 * FURTHER NOTE:
 * binary nodes: [BTOR_AND_NODE, ..., BTOR_LAMBDA_NODE]
 * ternary nodes: [BTOR_BCOND_NODE]
 * commutative nodes: [BTOR_AND_NODE, ..., BTOR_MUL_NODE]
 */
enum BtorNodeKind
{
  /* Even though the following is just for debugging purposes,
   * we should not put '#ifndef NDEBUG' around.  This would
   * make delta debugging of Heisenbugs in release mode more
   * difficult.
   */
  BTOR_INVALID_NODE  = 0,
  BTOR_BV_CONST_NODE = 1,
  BTOR_BV_VAR_NODE   = 2,
  BTOR_PARAM_NODE    = 3, /* parameter for lambda expressions */
  BTOR_SLICE_NODE    = 4,
  BTOR_AND_NODE      = 5,
  BTOR_BEQ_NODE      = 6, /* equality on bit vectors */
  BTOR_FEQ_NODE      = 7, /* equality on arrays */
  BTOR_ADD_NODE      = 8,
  BTOR_MUL_NODE      = 9,
  BTOR_ULT_NODE      = 10,
  BTOR_SLL_NODE      = 11,
  BTOR_SRL_NODE      = 12,
  BTOR_UDIV_NODE     = 13,
  BTOR_UREM_NODE     = 14,
  BTOR_CONCAT_NODE   = 15,
  BTOR_APPLY_NODE    = 16,
  BTOR_FORALL_NODE   = 17,
  BTOR_EXISTS_NODE   = 18,
  BTOR_LAMBDA_NODE   = 19, /* lambda expression */
  BTOR_BCOND_NODE    = 20, /* conditional on bit vectors */
  BTOR_ARGS_NODE     = 21,
  BTOR_UF_NODE       = 22,
  BTOR_PROXY_NODE    = 23, /* simplified expression without children */
  BTOR_NUM_OPS_NODE  = 24

  // NOTE: do not change this without changing 'g_btor_op2string' too ...
};

typedef enum BtorNodeKind BtorNodeKind;

extern const char *const g_btor_op2str[BTOR_NUM_OPS_NODE];

#define BTOR_BV_NODE_STRUCT                                                \
  struct                                                                   \
  {                                                                        \
    BtorNodeKind kind : 5;        /* kind of expression */                 \
    uint8_t mark : 2;             /* for DAG traversal */                  \
    uint8_t aux_mark : 2;         /* auxiliary mark flag */                \
    uint8_t beta_mark : 2;        /* mark for beta_reduce */               \
    uint8_t eval_mark : 2;        /* mark for eval_exp */                  \
    uint8_t clone_mark : 2;       /* mark for clone_exp_tree */            \
    uint8_t constraint : 1;       /* top level constraint ? */             \
    uint8_t erased : 1;           /* for debugging purposes */             \
    uint8_t disconnected : 1;     /* for debugging purposes */             \
    uint8_t unique : 1;           /* in unique table? */                   \
    uint8_t bytes;                /* allocated bytes */                    \
    uint8_t parameterized : 1;    /* param as sub expression ? */          \
    uint8_t lambda_below : 1;     /* lambda as sub expression ? */         \
    uint8_t quantifier_below : 1; /* quantifier as sub expression ? */     \
    uint8_t apply_below : 1;      /* apply as sub expression ? */          \
    uint8_t propagated : 1;       /* is set during propagation */          \
    uint8_t is_array : 1;         /* function represents array ? */        \
    uint8_t arity : 2;            /* arity of operator (at most 3) */      \
    int32_t id;                   /* unique expression id */               \
    uint32_t refs;                /* reference counter (incl. ext_refs) */ \
    uint32_t ext_refs;            /* external references counter */        \
    uint32_t parents;             /* number of parents */                  \
    BtorSortId sort_id;           /* sort id */                            \
    union                                                                  \
    {                                                                      \
      BtorAIGVec *av;        /* synthesized AIG vector */                  \
      BtorPtrHashTable *rho; /* for finding array conflicts */             \
    };                                                                     \
    BtorNode *next;         /* next in unique table */                     \
    BtorNode *simplified;   /* simplified expression */                    \
    Btor *btor;             /* boolector instance */                       \
    BtorNode *first_parent; /* head of parent list */                      \
    BtorNode *last_parent;  /* tail of parent list */                      \
  }

#define BTOR_BV_ADDITIONAL_NODE_STRUCT                             \
  struct                                                           \
  {                                                                \
    BtorNode *e[3];           /* expression children */            \
    BtorNode *prev_parent[3]; /* prev in parent list of child i */ \
    BtorNode *next_parent[3]; /* next in parent list of child i */ \
  }

struct BtorBVVarNode
{
  BTOR_BV_NODE_STRUCT;
  int32_t btor_id; /* id as defined in btor input */
};

typedef struct BtorBVVarNode BtorBVVarNode;

struct BtorUFNode
{
  BTOR_BV_NODE_STRUCT;
  int32_t btor_id; /* id as defined in btor input */
};

typedef struct BtorUFNode BtorUFNode;

struct BtorBVConstNode
{
  BTOR_BV_NODE_STRUCT;
  BtorBitVector *bits;
  BtorBitVector *invbits;
};

typedef struct BtorBVConstNode BtorBVConstNode;

struct BtorSliceNode
{
  BTOR_BV_NODE_STRUCT;
  BTOR_BV_ADDITIONAL_NODE_STRUCT;
  uint32_t upper;
  uint32_t lower;
};

typedef struct BtorSliceNode BtorSliceNode;

struct BtorBVNode
{
  BTOR_BV_NODE_STRUCT;
  BTOR_BV_ADDITIONAL_NODE_STRUCT;
};

typedef struct BtorBVNode BtorBVNode;

struct BtorNode
{
  BTOR_BV_NODE_STRUCT;
  BTOR_BV_ADDITIONAL_NODE_STRUCT;
};

#define BTOR_BINDER_STRUCT                                   \
  struct                                                     \
  {                                                          \
    BTOR_BV_NODE_STRUCT;                                     \
    BTOR_BV_ADDITIONAL_NODE_STRUCT;                          \
    BtorNode *body; /* short-cut for curried binder terms */ \
  }

struct BtorBinderNode
{
  BTOR_BINDER_STRUCT;
};

typedef struct BtorBinderNode BtorBinderNode;

struct BtorLambdaNode
{
  BTOR_BINDER_STRUCT;
  BtorPtrHashTable *static_rho;
};

typedef struct BtorLambdaNode BtorLambdaNode;

struct BtorParamNode
{
  BTOR_BV_NODE_STRUCT;
  BtorNode *binder; /* exp that binds the param (lambda, forall, exists) */
  BtorNode *assigned_exp;
};

typedef struct BtorParamNode BtorParamNode;

struct BtorArgsNode
{
  BTOR_BV_NODE_STRUCT;
  BTOR_BV_ADDITIONAL_NODE_STRUCT;
};

typedef struct BtorArgsNode BtorArgsNode;

#define BTOR_IS_INVALID_NODE_KIND(kind) ((kind) == BTOR_INVALID_NODE)

#define BTOR_IS_AND_NODE_KIND(kind) ((kind) == BTOR_AND_NODE)

#define BTOR_IS_SLICE_NODE_KIND(kind) ((kind) == BTOR_SLICE_NODE)

#define BTOR_IS_BV_CONST_NODE_KIND(kind) ((kind) == BTOR_BV_CONST_NODE)

#define BTOR_IS_BV_VAR_NODE_KIND(kind) ((kind) == BTOR_BV_VAR_NODE)

#define BTOR_IS_PARAM_NODE_KIND(kind) ((kind) == BTOR_PARAM_NODE)

#define BTOR_IS_BV_EQ_NODE_KIND(kind) (kind == BTOR_BEQ_NODE)

#define BTOR_IS_FUN_EQ_NODE_KIND(kind) (kind == BTOR_FEQ_NODE)

#define BTOR_IS_ULT_NODE_KIND(kind) (kind == BTOR_ULT_NODE)

#define BTOR_IS_FEQ_NODE_KIND(kind) (kind == BTOR_FEQ_NODE)

#define BTOR_IS_MUL_NODE_KIND(kind) ((kind) == BTOR_MUL_NODE)

#define BTOR_IS_ADD_NODE_KIND(kind) ((kind) == BTOR_ADD_NODE)

#define BTOR_IS_MUL_NODE_KIND(kind) ((kind) == BTOR_MUL_NODE)

#define BTOR_IS_UDIV_NODE_KIND(kind) ((kind) == BTOR_UDIV_NODE)

#define BTOR_IS_UREM_NODE_KIND(kind) ((kind) == BTOR_UREM_NODE)

#define BTOR_IS_FORALL_NODE_KIND(kind) ((kind) == BTOR_FORALL_NODE)

#define BTOR_IS_EXISTS_NODE_KIND(kind) ((kind) == BTOR_EXISTS_NODE)

#define BTOR_IS_LAMBDA_NODE_KIND(kind) ((kind) == BTOR_LAMBDA_NODE)

#define BTOR_IS_BCOND_NODE_KIND(kind) ((kind) == BTOR_BCOND_NODE)

#define BTOR_IS_UF_NODE_KIND(kind) ((kind) == BTOR_UF_NODE)

#define BTOR_IS_ARGS_NODE_KIND(kind) ((kind) == BTOR_ARGS_NODE)

#define BTOR_IS_APPLY_NODE_KIND(kind) ((kind) == BTOR_APPLY_NODE)

#define BTOR_IS_BV_COND_NODE_KIND(kind) (kind == BTOR_BCOND_NODE)

#define BTOR_IS_PROXY_NODE_KIND(kind) ((kind) == BTOR_PROXY_NODE)

#define BTOR_IS_CONCAT_NODE_KIND(kind) ((kind) == BTOR_CONCAT_NODE)

#define BTOR_IS_UNARY_NODE_KIND(kind) ((kind) == BTOR_SLICE_NODE)

#define BTOR_IS_BINARY_NODE_KIND(kind) \
  ((((kind) >= BTOR_AND_NODE) && ((kind) <= BTOR_LAMBDA_NODE)))

#define BTOR_IS_BINARY_COMMUTATIVE_NODE_KIND(kind) \
  (((kind) >= BTOR_AND_NODE) && ((kind) <= BTOR_MUL_NODE))

#define BTOR_IS_TERNARY_NODE_KIND(kind) (((kind) >= BTOR_BCOND_NODE))

#define BTOR_IS_INVALID_NODE(exp) \
  ((exp) && BTOR_IS_INVALID_NODE_KIND ((exp)->kind))

#define BTOR_IS_AND_NODE(exp) ((exp) && BTOR_IS_AND_NODE_KIND ((exp)->kind))

#define BTOR_IS_SLICE_NODE(exp) ((exp) && BTOR_IS_SLICE_NODE_KIND ((exp)->kind))
#define BTOR_IS_BV_CONST_NODE(exp) \
  ((exp) && BTOR_IS_BV_CONST_NODE_KIND ((exp)->kind))

#define BTOR_IS_BV_VAR_NODE(exp) \
  ((exp) && BTOR_IS_BV_VAR_NODE_KIND ((exp)->kind))

#define BTOR_IS_PARAM_NODE(exp) ((exp) && BTOR_IS_PARAM_NODE_KIND ((exp)->kind))

#define BTOR_IS_BV_EQ_NODE(exp) ((exp) && BTOR_IS_BV_EQ_NODE_KIND ((exp)->kind))

#define BTOR_IS_FUN_EQ_NODE(exp) \
  ((exp) && BTOR_IS_FUN_EQ_NODE_KIND ((exp)->kind))

#define BTOR_IS_ULT_NODE(exp) ((exp) && BTOR_IS_ULT_NODE_KIND ((exp)->kind))

#define BTOR_IS_FEQ_NODE(exp) ((exp) && BTOR_IS_FEQ_NODE_KIND ((exp)->kind))

#define BTOR_IS_ARRAY_OR_BV_EQ_NODE(exp) \
  (BTOR_IS_FEQ_NODE (exp) || BTOR_IS_BV_EQ_NODE (exp))

#define BTOR_IS_MUL_NODE(exp) ((exp) && BTOR_IS_MUL_NODE_KIND ((exp)->kind))

#define BTOR_IS_ADD_NODE(exp) ((exp) && BTOR_IS_ADD_NODE_KIND ((exp)->kind))

#define BTOR_IS_MUL_NODE(exp) ((exp) && BTOR_IS_MUL_NODE_KIND ((exp)->kind))

#define BTOR_IS_UDIV_NODE(exp) ((exp) && BTOR_IS_UDIV_NODE_KIND ((exp)->kind))

#define BTOR_IS_UREM_NODE(exp) ((exp) && BTOR_IS_UREM_NODE_KIND ((exp)->kind))

#define BTOR_IS_FORALL_NODE(exp) \
  ((exp) && BTOR_IS_FORALL_NODE_KIND ((exp)->kind))

#define BTOR_IS_EXISTS_NODE(exp) \
  ((exp) && BTOR_IS_EXISTS_NODE_KIND ((exp)->kind))

#define BTOR_IS_LAMBDA_NODE(exp) \
  ((exp) && BTOR_IS_LAMBDA_NODE_KIND ((exp)->kind))

#define BTOR_IS_BCOND_NODE(exp) ((exp) && BTOR_IS_BCOND_NODE_KIND ((exp)->kind))

#define BTOR_IS_UF_NODE(exp) ((exp) && BTOR_IS_UF_NODE_KIND ((exp)->kind))

#define BTOR_IS_ARGS_NODE(exp) ((exp) && BTOR_IS_ARGS_NODE_KIND ((exp)->kind))

#define BTOR_IS_APPLY_NODE(exp) ((exp) && BTOR_IS_APPLY_NODE_KIND ((exp)->kind))

#define BTOR_IS_WRITE_NODE(exp) ((exp) && BTOR_IS_WRITE_NODE_KIND ((exp)->kind))

#define BTOR_IS_COND_NODE(exp) \
  ((exp) && BTOR_IS_BV_COND_NODE_KIND ((exp)->kind))

#define BTOR_IS_BV_COND_NODE(exp)   \
  ((exp) && BTOR_IS_COND_NODE (exp) \
   && btor_is_bitvec_sort (&exp->btor->sorts_unique_table, exp->sort_id))

#define BTOR_IS_PROXY_NODE(exp) ((exp) && BTOR_IS_PROXY_NODE_KIND ((exp)->kind))

#define BTOR_IS_CONCAT_NODE(exp) \
  ((exp) && BTOR_IS_CONCAT_NODE_KIND ((exp)->kind))

#define BTOR_IS_UNARY_NODE(exp) ((exp) && BTOR_IS_UNARY_NODE_KIND ((exp)->kind))

#define BTOR_IS_BINARY_NODE(exp) \
  ((exp) && BTOR_IS_BINARY_NODE_KIND ((exp)->kind))

#define BTOR_IS_BINARY_COMMUTATIVE_NODE(exp) \
  ((exp) && BTOR_IS_BINARY_COMMUTATIVE_NODE_KIND ((exp)->kind))

#define BTOR_IS_TERNARY_NODE(exp) \
  ((exp) && BTOR_IS_TERNARY_NODE_KIND ((exp)->kind))

#define BTOR_INVERT_NODE(exp) ((BtorNode *) (1ul ^ (unsigned long int) (exp)))

#define BTOR_IS_INVERTED_NODE(exp) (1ul & (unsigned long int) (exp))

#define BTOR_COND_INVERT_NODE(cond_exp, exp)           \
  ((BtorNode *) (((unsigned long int) (cond_exp) &1ul) \
                 ^ (unsigned long int) (exp)))

#define BTOR_REAL_ADDR_NODE(exp) \
  ((struct BtorNode *) (~3ul & (unsigned long int) (exp)))

#define BTOR_GET_ID_NODE(exp) \
  (BTOR_IS_INVERTED_NODE (exp) ? -BTOR_REAL_ADDR_NODE (exp)->id : (exp)->id)

#define BTOR_AIGVEC_NODE(btor, exp)                                     \
  (BTOR_IS_INVERTED_NODE (exp)                                          \
       ? btor_not_aigvec ((btor)->avmgr, BTOR_REAL_ADDR_NODE (exp)->av) \
       : btor_copy_aigvec ((btor)->avmgr, exp->av))

#define BTOR_BITS_NODE(mm, exp)                                              \
  (BTOR_IS_INVERTED_NODE (exp) ? btor_not_bv (mm, btor_const_get_bits (exp)) \
                               : btor_copy_bv (mm, btor_const_get_bits (exp)))

#define BTOR_TAG_NODE(exp, tag) \
  ((BtorNode *) ((unsigned long int) tag | (unsigned long int) (exp)))

#define BTOR_GET_TAG_NODE(exp) ((int) (3ul & (unsigned long int) (exp)))

#define BTOR_IS_REGULAR_NODE(exp) (!(3ul & (unsigned long int) (exp)))

#define BTOR_IS_SYNTH_NODE(exp) ((exp)->av != 0)

#define BTOR_IS_FUN_COND_NODE(exp) \
  (BTOR_IS_COND_NODE (exp)         \
   && btor_is_fun_sort (&exp->btor->sorts_unique_table, exp->sort_id))

#define BTOR_IS_FUN_NODE(exp)                         \
  (BTOR_IS_LAMBDA_NODE (exp) || BTOR_IS_UF_NODE (exp) \
   || BTOR_IS_FUN_COND_NODE (exp))

#define BTOR_IS_UF_ARRAY_NODE(exp) \
  ((exp) && BTOR_IS_UF_NODE (exp) && ((BtorUFNode *) exp)->is_array)

#define BTOR_IS_QUANTIFIER_NODE(exp)               \
  (BTOR_IS_FORALL_NODE (BTOR_REAL_ADDR_NODE (exp)) \
   || BTOR_IS_EXISTS_NODE (BTOR_REAL_ADDR_NODE (exp)))

#define BTOR_IS_BINDER_NODE(exp) \
  (BTOR_IS_QUANTIFIER_NODE (exp) \
   || BTOR_IS_LAMBDA_NODE (BTOR_REAL_ADDR_NODE (exp)))

/*------------------------------------------------------------------------*/

struct BtorNodePair
{
  BtorNode *exp1;
  BtorNode *exp2;
};

typedef struct BtorNodePair BtorNodePair;

BtorNodePair *btor_new_exp_pair (Btor *, BtorNode *, BtorNode *);

void btor_delete_exp_pair (Btor *, BtorNodePair *);

unsigned int btor_hash_exp_pair (BtorNodePair *);

int btor_compare_exp_pair (BtorNodePair *, BtorNodePair *);

/*------------------------------------------------------------------------*/

/* Compares two expression pairs by ID */
int btor_compare_exp_by_id (BtorNode *exp0, BtorNode *exp1);

/* Hashes expression by ID */
unsigned int btor_hash_exp_by_id (BtorNode *exp);

/*------------------------------------------------------------------------*/

void btor_set_btor_id (Btor *btor, BtorNode *exp, int id);

/*------------------------------------------------------------------------*/
/* Implicit precondition of all functions taking expressions as inputs:
 * The 'width' of all input expressions has to be greater than zero.
 */

/* Binary constant.
 * strlen(bits) > 0
 * width(result) = strlen(bits)
 */
BtorNode *btor_const_exp (Btor *btor, BtorBitVector *bits);

/* Binary constant representing 'width' zeros.
 * width > 0
 * width(result) = width
 */
BtorNode *btor_zero_exp (Btor *btor, uint32_t width);

/* Constant respresenting FALSE
 * width(result) = 1
 */
BtorNode *btor_false_exp (Btor *btor);

/* Binary constant representing 'width' ones.
 * width > 0
 * width(result) = width
 */
BtorNode *btor_ones_exp (Btor *btor, uint32_t width);

/* Constant respresenting TRUE
 * width(result) = 1
 */
BtorNode *btor_true_exp (Btor *btor);

/* Binary constant representing 1 with 'width' bits.
 * width > 0
 * width(result) = width
 */
BtorNode *btor_one_exp (Btor *btor, uint32_t width);

/* Binary constant representing the unsigned integer.
 * The constant is obtained by either truncating bits
 * or by unsigned extension (padding with zeroes).
 * width > 0
 */
BtorNode *btor_unsigned_exp (Btor *btor, uint32_t u, uint32_t width);

/* Binary constant representing the signed integer.
 * The constant is obtained by either truncating bits
 * or by signed extension (padding with ones).
 * width > 0
 */
BtorNode *btor_int_exp (Btor *emg, int32_t i, uint32_t width);

/* Variable representing 'width' bits.
 * width > 0
 * width(result) = width
 */
BtorNode *btor_var_exp (Btor *btor, uint32_t width, const char *symbol);

/* Lambda variable representing 'width' bits.
 * width > 0
 * width(result) = width
 */
BtorNode *btor_param_exp (Btor *btor, uint32_t width, const char *symbol);

/* Array of size 2 ^ 'index_width' with elements of width 'elem_width'.
 * elem_width > 0
 * index_width > 0
 */
BtorNode *btor_array_exp (Btor *btor,
                          uint32_t elem_width,
                          uint32_t index_width,
                          const char *symbol);

/* Uninterpreted function with sort 'sort'.
 */
BtorNode *btor_uf_exp (Btor *btor, BtorSortId sort, const char *symbol);

/* One's complement.
 * width(result) = width(exp)
 */
BtorNode *btor_not_exp (Btor *btor, BtorNode *exp);

/* Two's complement.
 * width(result) = width(exp)
 */
BtorNode *btor_neg_exp (Btor *btor, BtorNode *exp);

/* OR reduction.
 * width(result) = 1
 */
BtorNode *btor_redor_exp (Btor *btor, BtorNode *exp);

/* XOR reduction.
 * width(result) = 1
 */
BtorNode *btor_redxor_exp (Btor *btor, BtorNode *exp);

/* AND reduction.
 * width(result) = 1
 */
BtorNode *btor_redand_exp (Btor *btor, BtorNode *exp);

/* BtorSlice a sub-vector from 'upper' to 'lower'.
 * upper < width(exp)
 * lower >= 0
 * upper >= lower
 * width(result) = upper - lower + 1
 */
BtorNode *btor_slice_exp (Btor *btor,
                          BtorNode *exp,
                          uint32_t upper,
                          uint32_t lower);
BtorNode *btor_slice_exp_node (Btor *btor,
                               BtorNode *exp,
                               uint32_t upper,
                               uint32_t lower);

/* Unsigned extension of 'width' bits.
 * width >= 0
 * width(result) = width(exp) + width
 */
BtorNode *btor_uext_exp (Btor *btor, BtorNode *exp, uint32_t width);

/* Signed extension of 'width' bits (keep sign).
 * width >= 0
 * width(result) = width(exp) + width
 */
BtorNode *btor_sext_exp (Btor *btor, BtorNode *exp, uint32_t width);

/* Logical IMPLICATION.
 * width(e0) = width(e1) = 1
 * width(result) = 1
 */
BtorNode *btor_implies_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Logical EQUIVALENCE.
 * width(e0) = width(e1) = 1
 * width(result) = 1
 */
BtorNode *btor_iff_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Logical and bit-vector XOR.
 * width(e0) = width(e1)
 * width(result) = width(e0) = width(e1)
 */
BtorNode *btor_xor_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Logical and bit-vector XNOR.
 * width(e0) = width(e1)
 * width(result) = width(e0) = width(e1)
 */
BtorNode *btor_xnor_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Logical and bit-vector AND.
 * width(e0) = width(e1)
 * width(result) = width(e0) = width(e1)
 */
BtorNode *btor_and_exp (Btor *btor, BtorNode *e0, BtorNode *e1);
BtorNode *btor_and_exp_node (Btor *btor, BtorNode *e0, BtorNode *e1);

BtorNode *btor_and_n_exp (Btor *btor, BtorNode *args[], uint32_t argc);

/* Logical and bit-vector NAND.
 * width(e0) = width(e1)
 * width(result) = width(e0) = width(e1)
 */
BtorNode *btor_nand_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Logical and bit-vector OR.
 * width(e0) = width(e1)
 * width(result) = width(e0) = width(e1)
 */
BtorNode *btor_or_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Logical and bit-vector NOR.
 * width(e0) = width(e1)
 * width(result) = width(e0) = width(e1)
 */
BtorNode *btor_nor_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Bit-vector or array equality.
 * width(e0) = width(e1)
 * width(result) = 1
 */
BtorNode *btor_eq_exp (Btor *btor, BtorNode *e0, BtorNode *e1);
BtorNode *btor_eq_exp_node (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Bit-vector or array inequality.
 * width(e0) = width(e1)
 * width(result) = 1
 */
BtorNode *btor_ne_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Adder.
 * width(e0) = width(e1)
 * width(result) = width(e0) = width(e1)
 */
BtorNode *btor_add_exp (Btor *btor, BtorNode *e0, BtorNode *e1);
BtorNode *btor_add_exp_node (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Result represents if adding two unsigned operands leads to an overflow.
 * width(e0) = width(e1)
 * width(result) = 1
 */
BtorNode *btor_uaddo_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Result represents if adding two signed operands leads to an overflow.
 * width(e0) = width(e1)
 * width(result) = 1
 */
BtorNode *btor_saddo_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Multiplier.
 * width(e0) = width(e1)
 * width(result) = width(e0) = width(e1)
 */
BtorNode *btor_mul_exp (Btor *btor, BtorNode *e0, BtorNode *e1);
BtorNode *btor_mul_exp_node (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Result represents if multiplying two unsigned operands leads to an overflow.
 * width(e0) = width(e1)
 * width(result) = 1
 */
BtorNode *btor_umulo_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Result represents if multiplying two signed operands leads to an overflow.
 * width(e0) = width(e1)
 * width(result) = 1
 */
BtorNode *btor_smulo_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Unsigned less than.
 * width(e0) = width(e1)
 * width(result) = 1
 */
BtorNode *btor_ult_exp (Btor *btor, BtorNode *e0, BtorNode *e1);
BtorNode *btor_ult_exp_node (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Signed less than.
 * width(e0) = width(e1)
 * width(result) = 1
 */
BtorNode *btor_slt_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Unsigned less than or equal.
 * width(e0) = width(e1)
 * width(result) = 1
 */
BtorNode *btor_ulte_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Signed less than or equal.
 * width(e0) = width(e1)
 * width(result) = 1
 */
BtorNode *btor_slte_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Unsigned greater than.
 * width(e0) = width(e1)
 * width(result) = 1
 */
BtorNode *btor_ugt_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Signed greater than.
 * width(e0) = width(e1)
 * width(result) = 1
 */
BtorNode *btor_sgt_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Unsigned greater than or equal.
 * width(e0) = width(e1)
 * width(result) = 1
 */
BtorNode *btor_ugte_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Signed greater than or equal.
 * width(e0) = width(e1)
 * width(result) = 1
 */
BtorNode *btor_sgte_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Shift left logical.
 * is_power_of_2(width(e0))
 * width(e1) = log2(width(e0))
 * width(result) width(e0)
 */
BtorNode *btor_sll_exp (Btor *btor, BtorNode *e0, BtorNode *e1);
BtorNode *btor_sll_exp_node (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Shift right logical.
 * is_power_of_2(width(e0))
 * width(e1) = log2(width(e0))
 * width(result) = width(e0)
 */
BtorNode *btor_srl_exp (Btor *btor, BtorNode *e0, BtorNode *e1);
BtorNode *btor_srl_exp_node (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Shift right arithmetic.
 * is_power_of_2(width(e0))
 * width(e1) = log2(width(e0))
 * width(result) = width(e0)
 */
BtorNode *btor_sra_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Rotate left.
 * is_power_of_2(width(e0))
 * width(e1) = log2(width(e0))
 * width(result) = width(e0)
 */
BtorNode *btor_rol_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Rotate right.
 * is_power_of_2(width(e0))
 * width(e1) = log2(width(e0))
 * width(result) = width(e0)
 */
BtorNode *btor_ror_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Subtractor.
 * width(e0) = width(e1)
 * width(result) = width(e0) = width(e1)
 */
BtorNode *btor_sub_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Result represents if e0 - e1 leads to an overflow if both are unsigned.
 * width(e0) = width(e1)
 * width(result) = 1
 */
BtorNode *btor_usubo_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Result represents if e0 - e1 leads to an overflow if both are signed.
 * width(e0) = width(e1)
 * width(result) = 1
 */
BtorNode *btor_ssubo_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Unsigned divider.
 * width(e0) = width(e1)
 * width(result) = width(e0) = width(e1)
 */
BtorNode *btor_udiv_exp (Btor *btor, BtorNode *e0, BtorNode *e1);
BtorNode *btor_udiv_exp_node (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Signed divider.
 * width(e0) = width(e1)
 * width(result) = width(e0) = width(e1)
 */
BtorNode *btor_sdiv_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Result represents if e0 / e1 leads to an overflow if both are signed.
 * For example INT_MIN / -1.
 * width(e0) = width(e1)
 * width(result) = 1
 */
BtorNode *btor_sdivo_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Unsigned modulo.
 * width(e0) = width(e1)
 * width(result) = width(e0) = width(e1)
 */
BtorNode *btor_urem_exp (Btor *btor, BtorNode *e0, BtorNode *e1);
BtorNode *btor_urem_exp_node (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Signed modulo.
 * width(e0) = width(e1)
 * width(result) = width(e0) = width(e1)
 */
BtorNode *btor_srem_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Signed modulo variant.
 * width(e0) = width(e1)
 * width(result) = width(e0) = width(e1)
 */
BtorNode *btor_smod_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Concatenation.
 * width(result) = width(e0) + width(e1)
 */
BtorNode *btor_concat_exp (Btor *btor, BtorNode *e0, BtorNode *e1);
BtorNode *btor_concat_exp_node (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Array read on array 'e_array' at position 'e_index'.
 * index_width(e_array) = width(e_index)
 * width(result) = elem_width(e_array)
 */
BtorNode *btor_read_exp (Btor *btor, BtorNode *e_array, BtorNode *e_index);
BtorNode *btor_read_exp_node (Btor *btor, BtorNode *e_array, BtorNode *e_index);

/* Array write on array 'e_array' at position 'e_index' with value 'e_value'.
 * index_width(e_array) = width(e_index)
 * elem_width(e_array) = width(e_value)
 */
BtorNode *btor_write_exp (Btor *btor,
                          BtorNode *e_array,
                          BtorNode *e_index,
                          BtorNode *e_value);
BtorNode *btor_write_exp_node (Btor *btor,
                               BtorNode *e_array,
                               BtorNode *e_index,
                               BtorNode *e_value);

/* Lambda expression with variable 'e_param' bound in 'e_exp'.
 */
BtorNode *btor_lambda_exp (Btor *btor, BtorNode *param, BtorNode *body);
BtorNode *btor_lambda_exp_node (Btor *btor, BtorNode *param, BtorNode *body);

/* Forall expression with variable 'param' and 'body'. */
BtorNode *btor_forall_exp (Btor *btor, BtorNode *param, BtorNode *body);
BtorNode *btor_forall_exp_node (Btor *btor, BtorNode *param, BtorNode *body);
BtorNode *btor_forall_n_exp (Btor *btor,
                             BtorNode *params[],
                             int paramc,
                             BtorNode *body);

/* Exists expression with variable 'param' and 'body' */
BtorNode *btor_exists_exp (Btor *btor, BtorNode *param, BtorNode *body);
BtorNode *btor_exists_exp_node (Btor *btor, BtorNode *param, BtorNode *body);
BtorNode *btor_exists_n_exp (Btor *btor,
                             BtorNode *params[],
                             int paramc,
                             BtorNode *body);

#if 0
BtorNode *btor_invert_quantifier (Btor * btor, BtorNode * quantifier);
#endif

/* Function expression with 'paramc' number of parameters 'params' and a
 * function body 'exp'.
 */
BtorNode *btor_fun_exp (Btor *btor,
                        BtorNode *params[],
                        uint32_t paramc,
                        BtorNode *exp);

/* Apply expression that applies argument expression 'args' to 'fun'.
 */
BtorNode *btor_apply_exp (Btor *btor, BtorNode *fun, BtorNode *args);
BtorNode *btor_apply_exp_node (Btor *btor, BtorNode *fun, BtorNode *args);

/* Apply expression that applies 'argc' number of arguments to 'fun'.
 */
BtorNode *btor_apply_exps (Btor *btor,
                           BtorNode *args[],
                           uint32_t argc,
                           BtorNode *fun);

/* Argument expression with 'argc' arguments.
 */
BtorNode *btor_args_exp (Btor *btor, BtorNode *args[], uint32_t argc);

/* If-then-else.
 * width(e_cond) = 1
 * width(e_if) = width(e_else)
 * width(result) = width(e_if) = width(e_else)
 */
BtorNode *btor_cond_exp (Btor *btor,
                         BtorNode *e_cond,
                         BtorNode *e_if,
                         BtorNode *e_else);
BtorNode *btor_cond_exp_node (Btor *btor,
                              BtorNode *e_cond,
                              BtorNode *e_if,
                              BtorNode *e_else);

/* Increments bit-vector expression by one */
BtorNode *btor_inc_exp (Btor *btor, BtorNode *exp);

/* Decrements bit-vector expression by one */
BtorNode *btor_dec_exp (Btor *btor, BtorNode *exp);

/* Create binary or ternary expressions (no rewriting). */
BtorNode *btor_create_exp (Btor *btor,
                           BtorNodeKind kind,
                           BtorNode *e[],
                           uint32_t arity);

/*------------------------------------------------------------------------*/

/* Gets the bit width of a bit vector expression */
uint32_t btor_get_exp_width (Btor *btor, BtorNode *exp);

/* Gets the bit width of the array elements. */
uint32_t btor_get_fun_exp_width (Btor *btor, BtorNode *exp);

BtorBitVector *btor_const_get_bits (BtorNode *exp);
BtorBitVector *btor_const_get_invbits (BtorNode *exp);
void btor_const_set_bits (BtorNode *exp, BtorBitVector *bits);
void btor_const_set_invbits (BtorNode *exp, BtorBitVector *bits);

/* Determines if expression is an array or not. */
bool btor_is_array_exp (Btor *btor, BtorNode *exp);

/* Determines if expression is an uf or array variable or not. */
bool btor_is_uf_array_var_exp (Btor *btor, BtorNode *exp);

/* Determines if expression is an uf or not. */
bool btor_is_uf_exp (Btor *btor, BtorNode *exp);

/* Determines if expression is a bv variable or not. */
bool btor_is_bv_var_exp (Btor *btor, BtorNode *exp);

/* Gets the number of bits used by indices on 'e_array'. */
int btor_get_index_exp_width (Btor *btor, BtorNode *e_array);

/* Get the id of an expression. */
int btor_get_id (Btor *btor, BtorNode *exp);

/* Retrieve the exp (belonging to instance 'btor') that matches given id.
 * (Note: increases ref counter of returned match!) */
BtorNode *btor_match_node_by_id (Btor *btor, int32_t id);

/* Retrieve the exp (belonging to instance 'btor') that matches given
 * expression by id. This is intended to be used for handling expressions
 * of a cloned instance (in a clone and its parent, expressions
 * with the same id correspond to each other, i.e. initially, the cloned
 * expression is an identical copy of the parent expression).
 * (Note: increases ref counter of return match!) */
BtorNode *btor_match_node (Btor *btor, BtorNode *exp);

BtorNode *btor_get_node_by_id (Btor *btor, int32_t id);

BtorNode *btor_get_node_by_symbol (Btor *btor, const char *sym);

/* Gets the symbol of an expression. */
char *btor_get_symbol_exp (Btor *btor, BtorNode *exp);

/* Sets the symbol of an expression. */
void btor_set_symbol_exp (Btor *btor, BtorNode *exp, const char *symbol);

/* Determines if expression is a param or not. */
bool btor_is_param_exp (Btor *btor, BtorNode *exp);

/* Determines if expression is a lambda or not. */
bool btor_is_fun_exp (Btor *btor, BtorNode *exp);

/* Gets the number of arguments of lambda expression 'exp'. */
uint32_t btor_get_fun_arity (Btor *btor, BtorNode *exp);

/* Determines if expression is an argument expression or not. */
bool btor_is_args_exp (Btor *btor, BtorNode *exp);

/* Gets the number of arguments of an argument expression 'exp'. */
int btor_get_args_arity (Btor *btor, BtorNode *exp);

/* Returns static_rho of given lambda node. */
BtorPtrHashTable *btor_lambda_get_static_rho (BtorNode *lambda);

void btor_lambda_set_static_rho (BtorNode *lambda,
                                 BtorPtrHashTable *static_rho);

BtorPtrHashTable *btor_lambda_copy_static_rho (Btor *btor, BtorNode *lambda);

BtorNode *btor_binder_get_body (BtorNode *binder);
void btor_binder_set_body (BtorNode *binder, BtorNode *body);

/* Getter for BtorSliceNode fields */
uint32_t btor_slice_get_upper (BtorNode *slice);
uint32_t btor_slice_get_lower (BtorNode *slice);

BtorNode *btor_param_get_binder (BtorNode *param);
void btor_param_set_binder (BtorNode *param, BtorNode *binder);
bool btor_param_is_bound (BtorNode *param);

BtorNode *btor_param_get_assigned_exp (BtorNode *param);

BtorNode *btor_param_set_assigned_exp (BtorNode *param, BtorNode *exp);

bool btor_param_is_exists_var (BtorNode *param);

bool btor_param_is_forall_var (BtorNode *param);

bool btor_param_is_free (Btor *btor, BtorNode *param, BtorNode *term);

/* Copies expression (increments reference counter). */
BtorNode *btor_copy_exp (Btor *btor, BtorNode *exp);

/* Releases expression (decrements reference counter). */
void btor_release_exp (Btor *btor, BtorNode *exp);

/* Convert 'exp' to a proxy expression.
 * NOTE: 'exp' must be already simplified */
void btor_set_to_proxy_exp (Btor *btor, BtorNode *exp);

int btor_cmp_exp_by_id_qsort_desc (const void *p, const void *q);
int btor_cmp_exp_by_id_qsort_asc (const void *p, const void *q);

/*------------------------------------------------------------------------*/
/* These are only necessary in kind of internal wrapper code, which uses
 * the internal structure of expressions, e.g., BtorNode, but otherwise
 * works through the external API, e.g., BoolectorNode, particularly if
 * call backs are provided by the user which have the external view.
 * Consider for example the substitution functions in 'boolectormap.h'
 * which in turn is heavily used in the model checker 'btormc.c'.
 */
void btor_inc_exp_ext_ref_counter (Btor *btor, BtorNode *e);

void btor_dec_exp_ext_ref_counter (Btor *btor, BtorNode *e);

/*------------------------------------------------------------------------*/
#ifndef NDEBUG
/*------------------------------------------------------------------------*/

bool btor_precond_slice_exp_dbg (Btor *btor,
                                 BtorNode *exp,
                                 uint32_t upper,
                                 uint32_t lower);

bool btor_precond_regular_unary_bv_exp_dbg (Btor *btor, BtorNode *exp);

bool btor_precond_regular_binary_bv_exp_dbg (Btor *btor,
                                             BtorNode *e0,
                                             BtorNode *e1);

bool btor_precond_eq_exp_dbg (Btor *btor, BtorNode *e0, BtorNode *e1);

bool btor_precond_shift_exp_dbg (Btor *btor, BtorNode *e0, BtorNode *e1);

bool btor_precond_concat_exp_dbg (Btor *btor, BtorNode *e0, BtorNode *e1);

bool btor_precond_read_exp_dbg (Btor *btor,
                                BtorNode *e_array,
                                BtorNode *e_index);

bool btor_precond_write_exp_dbg (Btor *btor,
                                 BtorNode *e_array,
                                 BtorNode *e_index,
                                 BtorNode *e_value);

bool btor_precond_cond_exp_dbg (Btor *btor,
                                BtorNode *e_cond,
                                BtorNode *e_if,
                                BtorNode *e_else);

bool btor_precond_apply_exp_dbg (Btor *btor, BtorNode *fun, BtorNode *args);

/*------------------------------------------------------------------------*/
#endif
/*------------------------------------------------------------------------*/

#endif
