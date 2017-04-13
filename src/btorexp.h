/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2015 Armin Biere.
 *  Copyright (C) 2012-2017 Aina Niemetz.
 *  Copyright (C) 2012-2017 Mathias Preiner.
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
  BTOR_BV_EQ_NODE    = 6, /* equality on bit vectors */
  BTOR_FUN_EQ_NODE   = 7, /* equality on arrays */
  BTOR_ADD_NODE      = 8,
  BTOR_MUL_NODE      = 9,
  BTOR_ULT_NODE      = 10,
  BTOR_SLL_NODE      = 11,
  BTOR_SRL_NODE      = 12,
  BTOR_UDIV_NODE     = 13,
  BTOR_UREM_NODE     = 14,
  BTOR_CONCAT_NODE   = 15,
  BTOR_APPLY_NODE    = 16,
  BTOR_LAMBDA_NODE   = 17, /* lambda expression */
  BTOR_COND_NODE     = 18, /* conditional on bit vectors */
  BTOR_ARGS_NODE     = 19,
  BTOR_UF_NODE       = 20,
  BTOR_UPDATE_NODE   = 21,
  BTOR_PROXY_NODE    = 22, /* simplified expression without children */
  BTOR_NUM_OPS_NODE  = 23

  // NOTE: do not change this without changing 'g_btor_op2string' too ...
};

typedef enum BtorNodeKind BtorNodeKind;

extern const char *const g_btor_op2str[BTOR_NUM_OPS_NODE];

#define BTOR_BV_NODE_STRUCT                                             \
  struct                                                                \
  {                                                                     \
    BtorNodeKind kind : 5;     /* kind of expression */                 \
    uint8_t constraint : 1;    /* top level constraint ? */             \
    uint8_t erased : 1;        /* for debugging purposes */             \
    uint8_t disconnected : 1;  /* for debugging purposes */             \
    uint8_t unique : 1;        /* in unique table? */                   \
    uint8_t parameterized : 1; /* param as sub expression ? */          \
    uint8_t lambda_below : 1;  /* lambda as sub expression ? */         \
    uint8_t apply_below : 1;   /* apply as sub expression ? */          \
    uint8_t propagated : 1;    /* is set during propagation */          \
    uint8_t is_array : 1;      /* function represents array ? */        \
    uint8_t arity : 2;         /* arity of operator (at most 3) */      \
    uint8_t bytes;             /* allocated bytes */                    \
    int32_t id;                /* unique expression id */               \
    uint32_t refs;             /* reference counter (incl. ext_refs) */ \
    uint32_t ext_refs;         /* external references counter */        \
    uint32_t parents;          /* number of parents */                  \
    BtorSortId sort_id;        /* sort id */                            \
    union                                                               \
    {                                                                   \
      BtorAIGVec *av;        /* synthesized AIG vector */               \
      BtorPtrHashTable *rho; /* for finding array conflicts */          \
    };                                                                  \
    BtorNode *next;         /* next in unique table */                  \
    BtorNode *simplified;   /* simplified expression */                 \
    Btor *btor;             /* boolector instance */                    \
    BtorNode *first_parent; /* head of parent list */                   \
    BtorNode *last_parent;  /* tail of parent list */                   \
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
};

typedef struct BtorBVVarNode BtorBVVarNode;

struct BtorUFNode
{
  BTOR_BV_NODE_STRUCT;
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

struct BtorLambdaNode
{
  BTOR_BV_NODE_STRUCT;
  BTOR_BV_ADDITIONAL_NODE_STRUCT;
  BtorPtrHashTable *static_rho;
  BtorNode *body; /* function body (short-cut for curried lambdas) */
};

typedef struct BtorLambdaNode BtorLambdaNode;

struct BtorParamNode
{
  BTOR_BV_NODE_STRUCT;
  BtorNode *lambda_exp; /* 1:1 relation param:lambda_exp */
  BtorNode *assigned_exp;
};

typedef struct BtorParamNode BtorParamNode;

struct BtorArgsNode
{
  BTOR_BV_NODE_STRUCT;
  BTOR_BV_ADDITIONAL_NODE_STRUCT;
};

typedef struct BtorArgsNode BtorArgsNode;

/*------------------------------------------------------------------------*/

#define BTOR_INVERT_NODE(exp) ((BtorNode *) (1ul ^ (unsigned long int) (exp)))

#define BTOR_IS_INVERTED_NODE(exp) (1ul & (unsigned long int) (exp))

#define BTOR_COND_INVERT_NODE(cond_exp, exp)           \
  ((BtorNode *) (((unsigned long int) (cond_exp) &1ul) \
                 ^ (unsigned long int) (exp)))

#define BTOR_REAL_ADDR_NODE(exp) \
  ((struct BtorNode *) (~3ul & (unsigned long int) (exp)))

#define BTOR_AIGVEC_NODE(btor, exp)                                     \
  (BTOR_IS_INVERTED_NODE (exp)                                          \
       ? btor_not_aigvec ((btor)->avmgr, BTOR_REAL_ADDR_NODE (exp)->av) \
       : btor_copy_aigvec ((btor)->avmgr, exp->av))

#define BTOR_TAG_NODE(exp, tag) \
  ((BtorNode *) ((unsigned long int) tag | (unsigned long int) (exp)))

#define BTOR_IS_REGULAR_NODE(exp) (!(3ul & (unsigned long int) (exp)))

#define BTOR_IS_SYNTH_NODE(exp) ((exp)->av != 0)

/*------------------------------------------------------------------------*/

static inline bool
btor_is_unary_node_kind (BtorNodeKind kind)
{
  return kind == BTOR_SLICE_NODE;
}

static inline bool
btor_is_binary_node_kind (BtorNodeKind kind)
{
  return kind >= BTOR_AND_NODE && kind <= BTOR_LAMBDA_NODE;
}

static inline bool
btor_is_binary_commutative_node_kind (BtorNodeKind kind)
{
  return kind >= BTOR_AND_NODE && kind <= BTOR_MUL_NODE;
}

static inline bool
btor_is_ternary_node_kind (BtorNodeKind kind)
{
  return kind >= BTOR_COND_NODE;
}

static inline bool
btor_is_unary_node (const BtorNode *exp)
{
  assert (exp);
  return btor_is_unary_node_kind (BTOR_REAL_ADDR_NODE (exp)->kind);
}

static inline bool
btor_is_binary_node (const BtorNode *exp)
{
  assert (exp);
  return btor_is_binary_node_kind (BTOR_REAL_ADDR_NODE (exp)->kind);
}

static inline bool
btor_is_binary_commutative_node (const BtorNode *exp)
{
  assert (exp);
  return btor_is_binary_commutative_node_kind (BTOR_REAL_ADDR_NODE (exp)->kind);
}

static inline bool
btor_is_ternary_node (const BtorNode *exp)
{
  assert (exp);
  return btor_is_ternary_node_kind (BTOR_REAL_ADDR_NODE (exp)->kind);
}

static inline bool
btor_is_invalid_node (const BtorNode *exp)
{
  assert (exp);
  return BTOR_REAL_ADDR_NODE (exp)->kind == BTOR_INVALID_NODE;
}

static inline bool
btor_is_proxy_node (const BtorNode *exp)
{
  assert (exp);
  return BTOR_REAL_ADDR_NODE (exp)->kind == BTOR_PROXY_NODE;
}

static inline bool
btor_is_bv_const_node (const BtorNode *exp)
{
  assert (exp);
  return BTOR_REAL_ADDR_NODE (exp)->kind == BTOR_BV_CONST_NODE;
}

static inline bool
btor_is_bv_var_node (const BtorNode *exp)
{
  assert (exp);
  return BTOR_REAL_ADDR_NODE (exp)->kind == BTOR_BV_VAR_NODE;
}

static inline bool
btor_is_bv_eq_node (const BtorNode *exp)
{
  assert (exp);
  return BTOR_REAL_ADDR_NODE (exp)->kind == BTOR_BV_EQ_NODE;
}

static inline bool
btor_is_fun_eq_node (const BtorNode *exp)
{
  assert (exp);
  return BTOR_REAL_ADDR_NODE (exp)->kind == BTOR_FUN_EQ_NODE;
}

static inline bool
btor_is_and_node (const BtorNode *exp)
{
  assert (exp);
  return BTOR_REAL_ADDR_NODE (exp)->kind == BTOR_AND_NODE;
}

static inline bool
btor_is_ult_node (const BtorNode *exp)
{
  assert (exp);
  return BTOR_REAL_ADDR_NODE (exp)->kind == BTOR_ULT_NODE;
}

static inline bool
btor_is_add_node (const BtorNode *exp)
{
  assert (exp);
  return BTOR_REAL_ADDR_NODE (exp)->kind == BTOR_ADD_NODE;
}

static inline bool
btor_is_mul_node (const BtorNode *exp)
{
  assert (exp);
  return BTOR_REAL_ADDR_NODE (exp)->kind == BTOR_MUL_NODE;
}

static inline bool
btor_is_udiv_node (const BtorNode *exp)
{
  assert (exp);
  return BTOR_REAL_ADDR_NODE (exp)->kind == BTOR_UDIV_NODE;
}

static inline bool
btor_is_urem_node (const BtorNode *exp)
{
  assert (exp);
  return BTOR_REAL_ADDR_NODE (exp)->kind == BTOR_UREM_NODE;
}

static inline bool
btor_is_slice_node (const BtorNode *exp)
{
  assert (exp);
  return BTOR_REAL_ADDR_NODE (exp)->kind == BTOR_SLICE_NODE;
}

static inline bool
btor_is_concat_node (const BtorNode *exp)
{
  assert (exp);
  return BTOR_REAL_ADDR_NODE (exp)->kind == BTOR_CONCAT_NODE;
}

static inline bool
btor_is_cond_node (const BtorNode *exp)
{
  assert (exp);
  return BTOR_REAL_ADDR_NODE (exp)->kind == BTOR_COND_NODE;
}

bool btor_is_bv_cond_node (const BtorNode *exp);
bool btor_is_fun_cond_node (const BtorNode *exp);

static inline bool
btor_is_uf_node (const BtorNode *exp)
{
  assert (exp);
  return BTOR_REAL_ADDR_NODE (exp)->kind == BTOR_UF_NODE;
}

static inline bool
btor_is_array_node (const BtorNode *exp)
{
  assert (exp);
  return BTOR_REAL_ADDR_NODE (exp)->is_array == 1;
}

static inline bool
btor_is_lambda_node (const BtorNode *exp)
{
  assert (exp);
  return BTOR_REAL_ADDR_NODE (exp)->kind == BTOR_LAMBDA_NODE;
}

static inline bool
btor_is_update_node (const BtorNode *exp)
{
  assert (exp);
  return BTOR_REAL_ADDR_NODE (exp)->kind == BTOR_UPDATE_NODE;
}

static inline bool
btor_is_fun_node (const BtorNode *exp)
{
  return btor_is_lambda_node (exp) || btor_is_uf_node (exp)
         || btor_is_fun_cond_node (exp) || btor_is_update_node (exp);
}

static inline bool
btor_is_uf_array_node (const BtorNode *exp)
{
  return btor_is_uf_node (exp)
         && ((BtorUFNode *) BTOR_REAL_ADDR_NODE (exp))->is_array;
}

static inline bool
btor_is_param_node (const BtorNode *exp)
{
  assert (exp);
  return BTOR_REAL_ADDR_NODE (exp)->kind == BTOR_PARAM_NODE;
}

static inline bool
btor_is_args_node (const BtorNode *exp)
{
  assert (exp);
  return BTOR_REAL_ADDR_NODE (exp)->kind == BTOR_ARGS_NODE;
}

static inline bool
btor_is_apply_node (const BtorNode *exp)
{
  assert (exp);
  return BTOR_REAL_ADDR_NODE (exp)->kind == BTOR_APPLY_NODE;
}

static inline bool
btor_is_array_or_bv_eq_node (const BtorNode *exp)
{
  return btor_is_fun_eq_node (exp) || btor_is_bv_eq_node (exp);
}

/*------------------------------------------------------------------------*/

/* Get the id of an expression (negative if exp is inverted). */
static inline int32_t
btor_exp_get_id (const BtorNode *exp)
{
  assert (exp);
  return BTOR_IS_INVERTED_NODE (exp) ? -BTOR_REAL_ADDR_NODE (exp)->id : exp->id;
}

static inline int
btor_exp_get_tag (const BtorNode *exp)
{
  return (int) (3ul & (unsigned long int) (exp));
}

/*========================================================================*/

/* Copies expression (increments reference counter). */
BtorNode *btor_copy_exp (Btor *btor, BtorNode *exp);

/* Releases expression (decrements reference counter). */
void btor_release_exp (Btor *btor, BtorNode *exp);

/*------------------------------------------------------------------------*/

static inline BtorSortId
btor_exp_get_sort_id (const BtorNode *exp)
{
  assert (exp);
  return BTOR_REAL_ADDR_NODE (exp)->sort_id;
}

static inline void
btor_exp_set_sort_id (BtorNode *exp, BtorSortId id)
{
  assert (exp);
  BTOR_REAL_ADDR_NODE (exp)->sort_id = id;
}

/*------------------------------------------------------------------------*/

void btor_inc_exp_ext_ref_counter (Btor *btor, BtorNode *e);

void btor_dec_exp_ext_ref_counter (Btor *btor, BtorNode *e);

/*------------------------------------------------------------------------*/

/* Convert 'exp' to a proxy expression.
 * NOTE: 'exp' must be already simplified */
void btor_set_to_proxy_exp (Btor *btor, BtorNode *exp);

/*------------------------------------------------------------------------*/

/* Set parsed id (BTOR format only, needed for model output). */
void btor_exp_set_btor_id (Btor *btor, BtorNode *exp, int32_t id);

/* Get parsed id (BTOR format only, needed for model output). */
int32_t btor_exp_get_btor_id (BtorNode *exp);

/* Get the exp (belonging to instance 'btor') that matches given id.
 * Note: The main difference to 'btor_match_node_by_id' is that this function
 *       does NOT increase the reference counter, and passing and 'id' < 0
 *       will return an inverted node */
BtorNode *btor_get_node_by_id (Btor *btor, int32_t id);

/* Retrieve the exp (belonging to instance 'btor') that matches given id.
 * Note: increases ref counter of returned match!
 * Note: 'id' must be greater 0
 *       -> will not return a conditionally inverted node */
BtorNode *btor_match_node_by_id (Btor *btor, int32_t id);

/*------------------------------------------------------------------------*/

/* Gets the symbol of an expression. */
char *btor_get_symbol_exp (Btor *btor, const BtorNode *exp);

/* Sets the symbol of an expression. */
void btor_set_symbol_exp (Btor *btor, BtorNode *exp, const char *symbol);

/* Get the exp (belonging to instance 'btor') that matches given symbol.
 * Note: does NOT increase the ref counter */
BtorNode *btor_get_node_by_symbol (Btor *btor, const char *sym);

/* Retrieve the exp (belonging to instance 'btor') that matches given symbol.
 * Note: increases ref counter of returned match! */
BtorNode *btor_match_node_by_symbol (Btor *btor, const char *sym);

/*------------------------------------------------------------------------*/

/* Retrieve the exp (belonging to instance 'btor') that matches given
 * expression by id. This is intended to be used for handling expressions
 * of a cloned instance (in a clone and its parent, expressions
 * with the same id correspond to each other, i.e. initially, the cloned
 * expression is an identical copy of the parent expression).
 * (Note: increases ref counter of return match!) */
BtorNode *btor_match_node (Btor *btor, BtorNode *exp);

/*------------------------------------------------------------------------*/

/* Compares two expression pairs by ID */
int btor_compare_exp_by_id (const BtorNode *exp0, const BtorNode *exp1);
/* Compare function for expressions (by ID) to be used for qsort */
int btor_compare_exp_by_id_qsort_desc (const void *p, const void *q);
int btor_compare_exp_by_id_qsort_asc (const void *p, const void *q);

/* Hashes expression by ID */
unsigned int btor_hash_exp_by_id (const BtorNode *exp);

/*------------------------------------------------------------------------*/

/* Get the bit width of a bit vector expression */
uint32_t btor_get_exp_width (Btor *btor, const BtorNode *exp);
/* Get the bit width of the array elements / function return value. */
uint32_t btor_get_fun_exp_width (Btor *btor, const BtorNode *exp);
/* Get the index width of an array expression */
uint32_t btor_get_index_exp_width (Btor *btor, const BtorNode *e_array);

/*------------------------------------------------------------------------*/

BtorBitVector *btor_const_get_bits (BtorNode *exp);
BtorBitVector *btor_const_get_invbits (BtorNode *exp);
void btor_const_set_bits (BtorNode *exp, BtorBitVector *bits);
void btor_const_set_invbits (BtorNode *exp, BtorBitVector *bits);

/*------------------------------------------------------------------------*/

/* Gets the number of arguments of lambda expression 'exp'. */
uint32_t btor_get_fun_arity (Btor *btor, BtorNode *exp);

/* Gets the number of arguments of an argument expression 'exp'. */
int btor_get_args_arity (Btor *btor, BtorNode *exp);

/*------------------------------------------------------------------------*/

BtorNode *btor_lambda_get_body (BtorNode *lambda);
void btor_lambda_set_body (BtorNode *lambda, BtorNode *body);

BtorPtrHashTable *btor_lambda_get_static_rho (BtorNode *lambda);

void btor_lambda_set_static_rho (BtorNode *lambda,
                                 BtorPtrHashTable *static_rho);

BtorPtrHashTable *btor_lambda_copy_static_rho (Btor *btor, BtorNode *lambda);

void btor_lambda_delete_static_rho (Btor *btor, BtorNode *lambda);

/*------------------------------------------------------------------------*/

uint32_t btor_slice_get_upper (BtorNode *slice);
uint32_t btor_slice_get_lower (BtorNode *slice);

/*------------------------------------------------------------------------*/

BtorNode *btor_param_get_binding_lambda (BtorNode *param);

void btor_param_set_binding_lambda (BtorNode *param, BtorNode *lambda);

bool btor_param_is_bound (BtorNode *param);

BtorNode *btor_param_get_assigned_exp (BtorNode *param);

BtorNode *btor_param_set_assigned_exp (BtorNode *param, BtorNode *exp);

/*========================================================================*/

struct BtorNodePair
{
  BtorNode *exp1;
  BtorNode *exp2;
};

typedef struct BtorNodePair BtorNodePair;

BtorNodePair *btor_new_exp_pair (Btor *, BtorNode *, BtorNode *);

void btor_delete_exp_pair (Btor *, BtorNodePair *);

unsigned int btor_hash_exp_pair (const BtorNodePair *);

int btor_compare_exp_pair (const BtorNodePair *, const BtorNodePair *);

/*========================================================================*/

/* Implicit precondition of all functions taking expressions as inputs:
 * The 'width' of all input expressions has to be greater than zero.
 */

/* Binary constant.
 * strlen(bits) > 0
 * width(result) = strlen(bits)
 */
BtorNode *btor_const_exp (Btor *btor, const BtorBitVector *bits);

/* Binary constant representing zero.
 */
BtorNode *btor_zero_exp (Btor *btor, BtorSortId sort);

/* Binary constant representing all ones.
 */
BtorNode *btor_ones_exp (Btor *btor, BtorSortId sort);

/* Binary constant representing 1.
 */
BtorNode *btor_one_exp (Btor *btor, BtorSortId sort);

/* Constant respresenting TRUE
 * width(result) = 1
 */
BtorNode *btor_true_exp (Btor *btor);

/* Constant respresenting FALSE
 * width(result) = 1
 */
BtorNode *btor_false_exp (Btor *btor);

/* Binary constant representing the signed integer.
 * The constant is obtained by either truncating bits
 * or by signed extension (padding with ones).
 */
BtorNode *btor_int_exp (Btor *emg, int32_t i, BtorSortId sort);

/* Binary constant representing the unsigned integer.
 * The constant is obtained by either truncating bits
 * or by unsigned extension (padding with zeroes).
 */
BtorNode *btor_unsigned_exp (Btor *btor, uint32_t u, BtorSortId sort);

/* Bit-vector variable.
 */
BtorNode *btor_var_exp (Btor *btor, BtorSortId sort, const char *symbol);

/* Lambda variable.
 */
BtorNode *btor_param_exp (Btor *btor, BtorSortId sort, const char *symbol);

/* Array variable.
 */
BtorNode *btor_array_exp (Btor *btor, BtorSortId sort, const char *symbol);

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

/* Shift right logical.
 * is_power_of_2(width(e0))
 * width(e1) = log2(width(e0))
 * width(result) = width(e0)
 */
BtorNode *btor_srl_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

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

/* Array read on array 'e_array' at position 'e_index'.
 * index_width(e_array) = width(e_index)
 * width(result) = elem_width(e_array)
 */
BtorNode *btor_read_exp (Btor *btor, BtorNode *e_array, BtorNode *e_index);

/* Array write on array 'e_array' at position 'e_index' with value 'e_value'.
 * index_width(e_array) = width(e_index)
 * elem_width(e_array) = width(e_value)
 */
BtorNode *btor_write_exp (Btor *btor,
                          BtorNode *e_array,
                          BtorNode *e_index,
                          BtorNode *e_value);

BtorNode *btor_update_exp (Btor *btor,
                           BtorNode *fun,
                           BtorNode *args,
                           BtorNode *value);

/* Lambda expression with variable 'e_param' bound in 'e_exp'.
 */
BtorNode *btor_lambda_exp (Btor *btor, BtorNode *e_param, BtorNode *e_exp);

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

/* Increments bit-vector expression by one */
BtorNode *btor_inc_exp (Btor *btor, BtorNode *exp);

/* Decrements bit-vector expression by one */
BtorNode *btor_dec_exp (Btor *btor, BtorNode *exp);

/*------------------------------------------------------------------------*/

BtorNode *btor_slice_exp_node (Btor *btor,
                               BtorNode *exp,
                               uint32_t upper,
                               uint32_t lower);

BtorNode *btor_and_exp_node (Btor *btor, BtorNode *e0, BtorNode *e1);

BtorNode *btor_eq_exp_node (Btor *btor, BtorNode *e0, BtorNode *e1);

BtorNode *btor_add_exp_node (Btor *btor, BtorNode *e0, BtorNode *e1);

BtorNode *btor_mul_exp_node (Btor *btor, BtorNode *e0, BtorNode *e1);

BtorNode *btor_ult_exp_node (Btor *btor, BtorNode *e0, BtorNode *e1);

BtorNode *btor_sll_exp_node (Btor *btor, BtorNode *e0, BtorNode *e1);

BtorNode *btor_srl_exp_node (Btor *btor, BtorNode *e0, BtorNode *e1);

BtorNode *btor_udiv_exp_node (Btor *btor, BtorNode *e0, BtorNode *e1);

BtorNode *btor_urem_exp_node (Btor *btor, BtorNode *e0, BtorNode *e1);

BtorNode *btor_concat_exp_node (Btor *btor, BtorNode *e0, BtorNode *e1);

BtorNode *btor_read_exp_node (Btor *btor, BtorNode *e_array, BtorNode *e_index);

BtorNode *btor_write_exp_node (Btor *btor,
                               BtorNode *e_array,
                               BtorNode *e_index,
                               BtorNode *e_value);

BtorNode *btor_cond_exp_node (Btor *btor,
                              BtorNode *e_cond,
                              BtorNode *e_if,
                              BtorNode *e_else);

BtorNode *btor_apply_exp_node (Btor *btor, BtorNode *fun, BtorNode *args);

BtorNode *btor_lambda_exp_node (Btor *btor, BtorNode *param, BtorNode *body);

BtorNode *btor_create_exp (Btor *btor,
                           BtorNodeKind kind,
                           BtorNode *e[],
                           uint32_t arity);

/*------------------------------------------------------------------------*/
#ifndef NDEBUG
/*------------------------------------------------------------------------*/

bool btor_precond_slice_exp_dbg (Btor *btor,
                                 const BtorNode *exp,
                                 uint32_t upper,
                                 uint32_t lower);

bool btor_precond_regular_unary_bv_exp_dbg (Btor *btor, const BtorNode *exp);

bool btor_precond_regular_binary_bv_exp_dbg (Btor *btor,
                                             const BtorNode *e0,
                                             const BtorNode *e1);

bool btor_precond_eq_exp_dbg (Btor *btor,
                              const BtorNode *e0,
                              const BtorNode *e1);

bool btor_precond_shift_exp_dbg (Btor *btor,
                                 const BtorNode *e0,
                                 const BtorNode *e1);

bool btor_precond_concat_exp_dbg (Btor *btor,
                                  const BtorNode *e0,
                                  const BtorNode *e1);

bool btor_precond_read_exp_dbg (Btor *btor,
                                const BtorNode *e_array,
                                const BtorNode *e_index);

bool btor_precond_write_exp_dbg (Btor *btor,
                                 const BtorNode *e_array,
                                 const BtorNode *e_index,
                                 const BtorNode *e_value);

bool btor_precond_cond_exp_dbg (Btor *btor,
                                const BtorNode *e_cond,
                                const BtorNode *e_if,
                                const BtorNode *e_else);

bool btor_precond_apply_exp_dbg (Btor *btor,
                                 const BtorNode *fun,
                                 const BtorNode *args);

/*------------------------------------------------------------------------*/
#endif
/*------------------------------------------------------------------------*/

#endif
