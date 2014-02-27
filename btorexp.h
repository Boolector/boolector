/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2013 Armin Biere.
 *  Copyright (C) 2012-2013 Aina Niemetz.
 *  Copyright (C) 2012-2014 Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTOREXP_H_INCLUDED
#define BTOREXP_H_INCLUDED

#include "boolector.h"
#include "btoraigvec.h"
#include "btorhash.h"
#include "btorqueue.h"
#include "btorstack.h"

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
  BTOR_INVALID_NODE = 0,

  BTOR_BV_CONST_NODE  = 1,
  BTOR_BV_VAR_NODE    = 2,
  BTOR_ARRAY_VAR_NODE = 3,
  BTOR_PARAM_NODE     = 4, /* parameter for lambda expressions */
  BTOR_SLICE_NODE     = 5,
  BTOR_AND_NODE       = 6,
  BTOR_BEQ_NODE       = 7, /* equality on bit vectors */
  BTOR_AEQ_NODE       = 8, /* equality on arrays */
  BTOR_ADD_NODE       = 9,
  BTOR_MUL_NODE       = 10,
  BTOR_ULT_NODE       = 11,
  BTOR_SLL_NODE       = 12,
  BTOR_SRL_NODE       = 13,
  BTOR_UDIV_NODE      = 14,
  BTOR_UREM_NODE      = 15,
  BTOR_CONCAT_NODE    = 16,
  BTOR_APPLY_NODE     = 17,
  BTOR_LAMBDA_NODE    = 18, /* lambda expression */
  BTOR_BCOND_NODE     = 19, /* conditional on bit vectors */
  BTOR_ARGS_NODE      = 20,
  BTOR_PROXY_NODE     = 21, /* simplified expression without children */
  BTOR_NUM_OPS_NODE   = 22
};

typedef enum BtorNodeKind BtorNodeKind;

typedef struct BtorNodePair BtorNodePair;

#define BTOR_BV_NODE_STRUCT                                             \
  struct                                                                \
  {                                                                     \
    BtorNodeKind kind : 5;       /* kind of expression */               \
    unsigned int mark : 3;       /* for DAG traversal */                \
    unsigned int aux_mark : 2;   /* auxiliary mark flag */              \
    unsigned int occ_mark : 1;   /* occurrence check mark flag */       \
    unsigned int fun_mark : 1;   /* for bottom up function traversal */ \
    unsigned int beta_mark : 2;  /* mark for beta_reduce */             \
    unsigned int eval_mark : 2;  /* mark for eval_exp */                \
    unsigned int synth_mark : 2; /* mark for synthesize_exp */          \
    unsigned int reachable : 1;  /* reachable from root ? */            \
    unsigned int tseitin : 1;    /* tseitin encoded into SAT ? */       \
    unsigned int lazy_tseitin : 1;                                      \
    unsigned int vread : 1;         /* virtual read ? */                \
    unsigned int vread_index : 1;   /* index for two virtual reads ? */ \
    unsigned int constraint : 1;    /* top level constraint ? */        \
    unsigned int erased : 1;        /* for debugging purposes */        \
    unsigned int disconnected : 1;  /* for debugging purposes */        \
    unsigned int unique : 1;        /* in unique table? */              \
    unsigned int bytes : 9;         /* allocated bytes */               \
    unsigned int parameterized : 1; /* param as sub expression ? */     \
    unsigned int lambda_below : 1;  /* lambda as sub expression ? */    \
    unsigned int merge : 1;                                             \
    unsigned int is_write : 1;                                          \
    unsigned int is_read : 1;                                           \
    unsigned int propagated : 1;                                        \
    char *bits;    /* three-valued bits */                              \
    char *invbits; /* inverted three-valued bits */                     \
    int id;        /* unique expression id */                           \
    int len;       /* number of bits */                                 \
    int refs;      /* reference counter (incl. ext_refs) */             \
    int ext_refs;  /* external references counter */                    \
    int parents;   /* number of parents */                              \
    int arity;     /* arity of operator */                              \
    union                                                               \
    {                                                                   \
      BtorAIGVec *av;        /* synthesized AIG vector */               \
      BtorPtrHashTable *rho; /* for finding array conflicts */          \
    };                                                                  \
    BtorNode *next;         /* next in unique table */                  \
    BtorNode *parent;       /* parent pointer for BFS */                \
    BtorNode *simplified;   /* simplified expression */                 \
    Btor *btor;             /* boolector */                             \
    BtorNode *first_parent; /* head of parent list */                   \
    BtorNode *last_parent;  /* tail of parent list */                   \
  }

#define BTOR_BV_ADDITIONAL_NODE_STRUCT                                \
  struct                                                              \
  {                                                                   \
    struct                                                            \
    {                                                                 \
      char *symbol; /* symbol for output */                           \
      int upper;    /* upper index for slices */                      \
      union                                                           \
      {                                                               \
        int lower;            /* lower index for slices */            \
        BtorNodePair *vreads; /* virtual reads for array equalites */ \
      };                                                              \
    };                                                                \
    BtorNode *e[3];           /* expression children */               \
    BtorNode *prev_parent[3]; /* prev in parent list of child i */    \
    BtorNode *next_parent[3]; /* next in parent list of child i */    \
  }
// TODO: optimization of **e, **prev_parent, **next_parent memory allocation

struct BtorBVVarNode
{
  BTOR_BV_NODE_STRUCT;
  char *symbol;
};

typedef struct BtorBVVarNode BtorBVVarNode;

struct BtorArrayVarNode
{
  BTOR_BV_NODE_STRUCT;
  char *symbol;
  int index_len;
};

typedef struct BtorArrayVarNode BtorArrayVarNode;

struct BtorBVConstNode
{
  BTOR_BV_NODE_STRUCT;
};

typedef struct BtorBVConstNode BtorBVConstNode;

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
  BtorPtrHashTable *synth_apps;
  struct BtorLambdaNode *head; /* points to first lambda in the curried lambda
                                  chain */
  BtorNode *body;              /* function body */
  int num_params; /* number of params (> 1 in case of curried lambdas) */
};

typedef struct BtorLambdaNode BtorLambdaNode;

struct BtorParamNode
{
  BTOR_BV_NODE_STRUCT;
  char *symbol;
  BtorLambdaNode *lambda_exp; /* 1:1 relation param:lambda_exp */
  BtorNode *assigned_exp;
};

typedef struct BtorParamNode BtorParamNode;

struct BtorArgsNode
{
  BTOR_BV_NODE_STRUCT;
  BTOR_BV_ADDITIONAL_NODE_STRUCT;
  int num_args;
};

typedef struct BtorArgsNode BtorArgsNode;

#define BTOR_IS_AND_NODE_KIND(kind) ((kind) == BTOR_AND_NODE)

#define BTOR_IS_BV_CONST_NODE_KIND(kind) ((kind) == BTOR_BV_CONST_NODE)

#define BTOR_IS_BV_VAR_NODE_KIND(kind) ((kind) == BTOR_BV_VAR_NODE)

#define BTOR_IS_ARRAY_VAR_NODE_KIND(kind) (kind == BTOR_ARRAY_VAR_NODE)

#define BTOR_IS_PARAM_NODE_KIND(kind) ((kind) == BTOR_PARAM_NODE)

#define BTOR_IS_BV_EQ_NODE_KIND(kind) (kind == BTOR_BEQ_NODE)

#define BTOR_IS_ARRAY_EQ_NODE_KIND(kind) (kind == BTOR_AEQ_NODE)

#define BTOR_IS_LAMBDA_NODE_KIND(kind) ((kind) == BTOR_LAMBDA_NODE)

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

#define BTOR_IS_AND_NODE(exp) ((exp) && BTOR_IS_AND_NODE_KIND ((exp)->kind))

#define BTOR_IS_BV_CONST_NODE(exp) \
  ((exp) && BTOR_IS_BV_CONST_NODE_KIND ((exp)->kind))

#define BTOR_IS_BV_VAR_NODE(exp) \
  ((exp) && BTOR_IS_BV_VAR_NODE_KIND ((exp)->kind))

#define BTOR_IS_ARRAY_VAR_NODE(exp) \
  ((exp) && BTOR_IS_ARRAY_VAR_NODE_KIND ((exp)->kind))

#define BTOR_IS_PARAM_NODE(exp) ((exp) && BTOR_IS_PARAM_NODE_KIND ((exp)->kind))

#define BTOR_IS_BV_EQ_NODE(exp) ((exp) && BTOR_IS_BV_EQ_NODE_KIND ((exp)->kind))

#define BTOR_IS_ARRAY_EQ_NODE(exp) \
  ((exp) && BTOR_IS_ARRAY_EQ_NODE_KIND ((exp)->kind))

#define BTOR_IS_ARRAY_OR_BV_EQ_NODE(exp) \
  (BTOR_IS_ARRAY_EQ_NODE (exp) || BTOR_IS_BV_EQ_NODE (exp))

#define BTOR_IS_LAMBDA_NODE(exp) \
  ((exp) && BTOR_IS_LAMBDA_NODE_KIND ((exp)->kind))

#define BTOR_IS_ARGS_NODE(exp) ((exp) && BTOR_IS_ARGS_NODE_KIND ((exp)->kind))

#define BTOR_IS_APPLY_NODE(exp) ((exp) && BTOR_IS_APPLY_NODE_KIND ((exp)->kind))

#define BTOR_IS_WRITE_NODE(exp) ((exp) && BTOR_IS_WRITE_NODE_KIND ((exp)->kind))

#define BTOR_IS_ARRAY_COND_NODE(exp) \
  ((exp) && BTOR_IS_ARRAY_COND_NODE_KIND ((exp)->kind))

#define BTOR_IS_BV_COND_NODE(exp) \
  ((exp) && BTOR_IS_BV_COND_NODE_KIND ((exp)->kind))

#define BTOR_IS_PROXY_NODE(exp) ((exp) && BTOR_IS_PROXY_NODE_KIND ((exp)->kind))

#define BTOR_IS_CONCAT_NODE(exp) \
  ((exp) && BTOR_IS_CONCAT_NODE_KIND ((exp)->kind))

#define BTOR_IS_UNARY_NODE(exp) ((exp) && BTOR_IS_UNARY_NODE_KIND ((exp)->kind))

#define BTOR_IS_BINARY_NODE(exp) \
  ((exp) && BTOR_IS_BINARY_NODE_KIND ((exp)->kind))

#define BTOR_IS_TERNARY_NODE(exp) \
  ((exp) && BTOR_IS_TERNARY_NODE_KIND ((exp)->kind))

#define BTOR_INVERT_NODE(exp) ((BtorNode *) (1ul ^ (unsigned long int) (exp)))

#define BTOR_IS_INVERTED_NODE(exp) (1ul & (unsigned long int) (exp))

#define BTOR_COND_INVERT_NODE(cond_exp, exp)           \
  ((BtorNode *) (((unsigned long int) (cond_exp) &1ul) \
                 ^ (unsigned long int) (exp)))

#define BTOR_REAL_ADDR_NODE(exp) \
  ((BtorNode *) (~3ul & (unsigned long int) (exp)))

#define BTOR_GET_ID_NODE(exp) \
  (BTOR_IS_INVERTED_NODE (exp) ? -BTOR_REAL_ADDR_NODE (exp)->id : exp->id)

#define BTOR_AIGVEC_NODE(btor, exp)                                     \
  (BTOR_IS_INVERTED_NODE (exp)                                          \
       ? btor_not_aigvec ((btor)->avmgr, BTOR_REAL_ADDR_NODE (exp)->av) \
       : btor_copy_aigvec ((btor)->avmgr, exp->av))

#define BTOR_BITS_NODE(mm, exp)                               \
  (BTOR_IS_INVERTED_NODE (exp)                                \
       ? btor_not_const (mm, BTOR_REAL_ADDR_NODE (exp)->bits) \
       : btor_copy_const (mm, exp->bits))

#define BTOR_TAG_NODE(exp, tag) \
  ((BtorNode *) ((unsigned long int) tag | (unsigned long int) (exp)))

#define BTOR_GET_TAG_NODE(exp) ((int) (3ul & (unsigned long int) (exp)))

#define BTOR_IS_REGULAR_NODE(exp) (!(3ul & (unsigned long int) (exp)))

#define BTOR_IS_SYNTH_NODE(exp) ((exp)->av != 0)

#define BTOR_IS_CURRIED_LAMBDA_NODE(exp) \
  (BTOR_IS_LAMBDA_NODE (exp) && ((BtorLambdaNode *) exp)->head)

#define BTOR_IS_FIRST_CURRIED_LAMBDA(exp) \
  (BTOR_IS_LAMBDA_NODE (exp)              \
   && (((BtorLambdaNode *) exp)->head == (BtorLambdaNode *) exp))

#define BTOR_IS_FUN_NODE(exp) \
  (BTOR_IS_LAMBDA_NODE (exp) || BTOR_IS_ARRAY_VAR_NODE (exp))

#define BTOR_IS_BOUND_PARAM_NODE(exp) (((BtorParamNode *) exp)->lambda_exp != 0)

#define BTOR_PARAM_GET_LAMBDA_NODE(exp) (((BtorParamNode *) exp)->lambda_exp)

#define BTOR_PARAM_SET_LAMBDA_NODE(param, lambda) \
  (((BtorParamNode *) BTOR_REAL_ADDR_NODE (param))->lambda_exp = lambda)

#define BTOR_LAMBDA_GET_NESTED(exp) (((BtorLambdaNode *) exp)->head)

#define BTOR_LAMBDA_GET_PARAM(exp) (((BtorParamNode *) exp->e[0]))

#define BTOR_LAMBDA_GET_BODY(exp) (((BtorLambdaNode *) exp)->body)

#define BTOR_ARRAY_INDEX_LEN(exp)                                        \
  ((BTOR_IS_ARRAY_VAR_NODE (exp) ? ((BtorArrayVarNode *) exp)->index_len \
                                 : BTOR_LAMBDA_GET_PARAM (exp)->len))

/*------------------------------------------------------------------------*/

struct BtorNodePair
{
  BtorNode *exp1;
  BtorNode *exp2;
};

BtorNodePair *new_exp_pair (Btor *, BtorNode *, BtorNode *);

void delete_exp_pair (Btor *, BtorNodePair *);

unsigned int hash_exp_pair (BtorNodePair *);

int compare_exp_pair (BtorNodePair *, BtorNodePair *);

/*------------------------------------------------------------------------*/

/* Compares two expression pairs by ID */
int btor_compare_exp_by_id (BtorNode *exp0, BtorNode *exp1);

/* Hashes expression by ID */
unsigned int btor_hash_exp_by_id (BtorNode *exp);

/*------------------------------------------------------------------------*/
/* Implicit precondition of all functions taking expressions as inputs:
 * The length 'len' of all input expressions have to be greater than zero.
 */

/* Binary constant.
 * strlen(bits) > 0
 * len(result) = strlen(bits)
 */
BtorNode *btor_const_exp (Btor *btor, const char *bits);

/* Binary constant representing 'len' zeros.
 * len > 0
 * len(result) = len
 */
BtorNode *btor_zero_exp (Btor *btor, int len);

/* Constant respresenting FALSE
 * len(result) = 1
 */
BtorNode *btor_false_exp (Btor *btor);

/* Binary constant representing 'len' ones.
 * len > 0
 * len(result) = len
 */
BtorNode *btor_ones_exp (Btor *btor, int len);

/* Constant respresenting TRUE
 * len(result) = 1
 */
BtorNode *btor_true_exp (Btor *btor);

/* Binary constant representing 1 with 'len' bits.
 * len > 0
 * len(result) = len
 */
BtorNode *btor_one_exp (Btor *btor, int len);

/* Binary constant representing the unsigned integer.
 * The constant is obtained by either truncating bits
 * or by unsigned extension (padding with zeroes).
 * len > 0
 */
BtorNode *btor_unsigned_exp (Btor *btor, unsigned u, int len);

/* Binary constant representing the signed integer.
 * The constant is obtained by either truncating bits
 * or by signed extension (padding with ones).
 * len > 0
 */
BtorNode *btor_int_exp (Btor *emg, int i, int len);

/* Variable representing 'len' bits.
 * len > 0
 * len(result) = len
 */
BtorNode *btor_var_exp (Btor *btor, int len, const char *symbol);

/* Lambda variable representing 'len' bits.
 * len > 0
 * len(result) = len
 */
BtorNode *btor_param_exp (Btor *btor, int len, const char *symbol);

/* Array of size 2 ^ 'index_len' with elements of length 'elem_len'.
 * elem_len > 0
 * index_len > 0
 */
BtorNode *btor_array_exp (Btor *btor,
                          int elem_len,
                          int index_len,
                          const char *symbol);

/* One's complement.
 * len(result) = len(exp)
 */
BtorNode *btor_not_exp (Btor *btor, BtorNode *exp);

/* Two's complement.
 * len(result) = len(exp)
 */
BtorNode *btor_neg_exp (Btor *btor, BtorNode *exp);

/* OR reduction.
 * len(result) = 1
 */
BtorNode *btor_redor_exp (Btor *btor, BtorNode *exp);

/* XOR reduction.
 * len(result) = 1
 */
BtorNode *btor_redxor_exp (Btor *btor, BtorNode *exp);

/* AND reduction.
 * len(result) = 1
 */
BtorNode *btor_redand_exp (Btor *btor, BtorNode *exp);

/* BtorSlice a sub-vector from 'upper' to 'lower'.
 * upper < len(exp)
 * lower >= 0
 * upper >= lower
 * len(result) = upper - lower + 1
 */
BtorNode *btor_slice_exp (Btor *btor, BtorNode *exp, int upper, int lower);

/* Unsigned extension of 'len' bits.
 * len >= 0
 * len(result) = len(exp) + len
 */
BtorNode *btor_uext_exp (Btor *btor, BtorNode *exp, int len);

/* Signed extension of 'len' bits (keep sign).
 * len >= 0
 * len(result) = len(exp) + len
 */
BtorNode *btor_sext_exp (Btor *btor, BtorNode *exp, int len);

/* Logical IMPLICATION.
 * len(e0) = len(e1) = 1
 * len(result) = 1
 */
BtorNode *btor_implies_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Logical EQUIVALENCE.
 * len(e0) = len(e1) = 1
 * len(result) = 1
 */
BtorNode *btor_iff_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Logical and bit-vector XOR.
 * len(e0) = len(e1)
 * len(result) = len(e0) = len(e1)
 */
BtorNode *btor_xor_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Logical and bit-vector XNOR.
 * len(e0) = len(e1)
 * len(result) = len(e0) = len(e1)
 */
BtorNode *btor_xnor_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Logical and bit-vector AND.
 * len(e0) = len(e1)
 * len(result) = len(e0) = len(e1)
 */
BtorNode *btor_and_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Logical and bit-vector NAND.
 * len(e0) = len(e1)
 * len(result) = len(e0) = len(e1)
 */
BtorNode *btor_nand_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Logical and bit-vector OR.
 * len(e0) = len(e1)
 * len(result) = len(e0) = len(e1)
 */
BtorNode *btor_or_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Logical and bit-vector NOR.
 * len(e0) = len(e1)
 * len(result) = len(e0) = len(e1)
 */
BtorNode *btor_nor_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Bit-vector or array equality.
 * len(e0) = len(e1)
 * len(result) = 1
 */
BtorNode *btor_eq_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Bit-vector or array inequality.
 * len(e0) = len(e1)
 * len(result) = 1
 */
BtorNode *btor_ne_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Adder.
 * len(e0) = len(e1)
 * len(result) = len(e0) = len(e1)
 */
BtorNode *btor_add_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Result represents if adding two unsigned operands leads to an overflow.
 * len(e0) = len(e1)
 * len(result) = 1
 */
BtorNode *btor_uaddo_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Result represents if adding two signed operands leads to an overflow.
 * len(e0) = len(e1)
 * len(result) = 1
 */
BtorNode *btor_saddo_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Multiplier.
 * len(e0) = len(e1)
 * len(result) = len(e0) = len(e1)
 */
BtorNode *btor_mul_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Result represents if multiplying two unsigned operands leads to an overflow.
 * len(e0) = len(e1)
 * len(result) = 1
 */
BtorNode *btor_umulo_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Result represents if multiplying two signed operands leads to an overflow.
 * len(e0) = len(e1)
 * len(result) = 1
 */
BtorNode *btor_smulo_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Unsigned less than.
 * len(e0) = len(e1)
 * len(result) = 1
 */
BtorNode *btor_ult_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Signed less than.
 * len(e0) = len(e1)
 * len(result) = 1
 */
BtorNode *btor_slt_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Unsigned less than or equal.
 * len(e0) = len(e1)
 * len(result) = 1
 */
BtorNode *btor_ulte_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Signed less than or equal.
 * len(e0) = len(e1)
 * len(result) = 1
 */
BtorNode *btor_slte_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Unsigned greater than.
 * len(e0) = len(e1)
 * len(result) = 1
 */
BtorNode *btor_ugt_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Signed greater than.
 * len(e0) = len(e1)
 * len(result) = 1
 */
BtorNode *btor_sgt_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Unsigned greater than or equal.
 * len(e0) = len(e1)
 * len(result) = 1
 */
BtorNode *btor_ugte_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Signed greater than or equal.
 * len(e0) = len(e1)
 * len(result) = 1
 */
BtorNode *btor_sgte_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Shift left logical.
 * is_power_of_2(len(e0))
 * len(e1) = log2(len(e0))
 * len(result) len(e0)
 */
BtorNode *btor_sll_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Shift right logical.
 * is_power_of_2(len(e0))
 * len(e1) = log2(len(e0))
 * len(result) = len(e0)
 */
BtorNode *btor_srl_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Shift right arithmetic.
 * is_power_of_2(len(e0))
 * len(e1) = log2(len(e0))
 * len(result) = len(e0)
 */
BtorNode *btor_sra_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Rotate left.
 * is_power_of_2(len(e0))
 * len(e1) = log2(len(e0))
 * len(result) = len(e0)
 */
BtorNode *btor_rol_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Rotate right.
 * is_power_of_2(len(e0))
 * len(e1) = log2(len(e0))
 * len(result) = len(e0)
 */
BtorNode *btor_ror_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Subtractor.
 * len(e0) = len(e1)
 * len(result) = len(e0) = len(e1)
 */
BtorNode *btor_sub_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Result represents if e0 - e1 leads to an overflow if both are unsigned.
 * len(e0) = len(e1)
 * len(result) = 1
 */
BtorNode *btor_usubo_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Result represents if e0 - e1 leads to an overflow if both are signed.
 * len(e0) = len(e1)
 * len(result) = 1
 */
BtorNode *btor_ssubo_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Unsigned divider.
 * len(e0) = len(e1)
 * len(result) = len(e0) = len(e1)
 */
BtorNode *btor_udiv_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Signed divider.
 * len(e0) = len(e1)
 * len(result) = len(e0) = len(e1)
 */
BtorNode *btor_sdiv_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Result represents if e0 / e1 leads to an overflow if both are signed.
 * For example INT_MIN / -1.
 * len(e0) = len(e1)
 * len(result) = 1
 */
BtorNode *btor_sdivo_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Unsigned modulo.
 * len(e0) = len(e1)
 * len(result) = len(e0) = len(e1)
 */
BtorNode *btor_urem_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Signed modulo.
 * len(e0) = len(e1)
 * len(result) = len(e0) = len(e1)
 */
BtorNode *btor_srem_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Signed modulo variant.
 * len(e0) = len(e1)
 * len(result) = len(e0) = len(e1)
 */
BtorNode *btor_smod_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Concatenation.
 * len(result) = len(e0) + len(e1)
 */
BtorNode *btor_concat_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Array read on array 'e_array' at position 'e_index'.
 * index_len(e_array) = len(e_index)
 * len(result) = elem_len(e_array)
 */
BtorNode *btor_read_exp (Btor *btor, BtorNode *e_array, BtorNode *e_index);

/* Array write on array 'e_array' at position 'e_index' with value 'e_value'.
 * index_len(e_array) = len(e_index)
 * elem_len(e_array) = len(e_value)
 */
BtorNode *btor_write_exp (Btor *btor,
                          BtorNode *e_array,
                          BtorNode *e_index,
                          BtorNode *e_value);

/* Lambda expression with variable 'e_param' bound in 'e_exp'.
 */
BtorNode *btor_lambda_exp (Btor *btor, BtorNode *e_param, BtorNode *e_exp);

/* Function expression with 'paramc' number of parameters 'params' and a
 * function body 'exp'.
 */
BtorNode *btor_fun_exp (Btor *btor,
                        int paramc,
                        BtorNode **params,
                        BtorNode *exp);

/* Apply expression that applies argument expression 'args' to 'fun'.
 */
BtorNode *btor_apply_exp (Btor *btor, BtorNode *fun, BtorNode *args);

/* Apply expression that applies 'argc' number of arguments to 'fun'.
 */
BtorNode *btor_apply_exps (Btor *btor,
                           int argc,
                           BtorNode **args,
                           BtorNode *fun);

/* Argument expression with 'argc' arguments.
 */
BtorNode *btor_args_exp (Btor *btor, int argc, BtorNode **args);

/* If-then-else.
 * len(e_cond) = 1
 * len(e_if) = len(e_else)
 * len(result) = len(e_if) = len(e_else)
 */
BtorNode *btor_cond_exp (Btor *btor,
                         BtorNode *e_cond,
                         BtorNode *e_if,
                         BtorNode *e_else);

/* Increments bit-vector expression by one */
BtorNode *btor_inc_exp (Btor *btor, BtorNode *exp);

/* Decrements bit-vector expression by one */
BtorNode *btor_dec_exp (Btor *btor, BtorNode *exp);

/* Gets the length of an expression representing the number of bits. */
int btor_get_exp_len (Btor *btor, BtorNode *exp);

/* Determines if expression is an array or not. */
int btor_is_array_exp (Btor *btor, BtorNode *exp);

/* Determines if expression is an array variable or not. */
int btor_is_array_var_exp (Btor *btor, BtorNode *exp);

/* Gets the number of bits used by indices on 'e_array'. */
int btor_get_index_exp_len (Btor *btor, BtorNode *e_array);

/* Gets the symbol of a variable. */
char *btor_get_symbol_exp (Btor *btor, BtorNode *exp);

/* Determines if expression is a param or not. */
int btor_is_param_exp (Btor *btor, BtorNode *exp);

/* Determines if param is already bound to a lambda expression or not. */
int btor_is_bound_param_exp (Btor *btor, BtorNode *param);

/* Determines if expression is a lambda or not. */
int btor_is_fun_exp (Btor *btor, BtorNode *exp);

/* Gets the number of arguments of lambda expression 'exp'. */
int btor_get_fun_arity (Btor *btor, BtorNode *exp);

/* Determines if expression is an argument expression or not. */
int btor_is_args_exp (Btor *btor, BtorNode *exp);

/* Gets the number of arguments of an argument expression 'exp'. */
int btor_get_args_arity (Btor *btor, BtorNode *exp);

/* Copies expression (increments reference counter). */
BtorNode *btor_copy_exp (Btor *btor, BtorNode *exp);

/* Releases expression (decrements reference counter). */
void btor_release_exp (Btor *btor, BtorNode *exp);

/* Convert 'exp' to a proxy expression.
 * NOTE: 'exp' must be already simplified */
void btor_set_to_proxy_exp (Btor *btor, BtorNode *exp);

/*------------------------------------------------------------------------*/

BtorNode *btor_slice_exp_node (Btor *btor, BtorNode *exp, int upper, int lower);

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

/*------------------------------------------------------------------------*/
#ifndef NDEBUG
/*------------------------------------------------------------------------*/

int btor_precond_slice_exp_dbg (const Btor *btor,
                                const BtorNode *exp,
                                int upper,
                                int lower);

int btor_precond_regular_unary_bv_exp_dbg (const Btor *btor,
                                           const BtorNode *exp);

int btor_precond_regular_binary_bv_exp_dbg (const Btor *btor,
                                            const BtorNode *e0,
                                            const BtorNode *e1);

int btor_precond_eq_exp_dbg (const Btor *btor,
                             const BtorNode *e0,
                             const BtorNode *e1);

int btor_precond_shift_exp_dbg (const Btor *btor,
                                const BtorNode *e0,
                                const BtorNode *e1);

int btor_precond_concat_exp_dbg (const Btor *btor,
                                 const BtorNode *e0,
                                 const BtorNode *e1);

int btor_precond_read_exp_dbg (const Btor *btor,
                               const BtorNode *e_array,
                               const BtorNode *e_index);

int btor_precond_write_exp_dbg (const Btor *btor,
                                const BtorNode *e_array,
                                const BtorNode *e_index,
                                const BtorNode *e_value);

int btor_precond_cond_exp_dbg (const Btor *btor,
                               const BtorNode *e_cond,
                               const BtorNode *e_if,
                               const BtorNode *e_else);
/*------------------------------------------------------------------------*/
#endif
/*------------------------------------------------------------------------*/

#endif
