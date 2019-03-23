/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2015 Armin Biere.
 *  Copyright (C) 2012-2019 Aina Niemetz.
 *  Copyright (C) 2012-2017 Mathias Preiner.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORNODE_H_INCLUDED
#define BTORNODE_H_INCLUDED

#include "btoraigvec.h"
#include "btorbv.h"
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

/* NOTE: DO NOT REORDER THE INDICES.
 * CERTAIN MACROS DEPEND ON ORDER.
 * Some code also depends on that BTOR_INVALID_NODE, BTOR_CONST_NODE
 * and BTOR_VAR_NODE are at the beginning,
 * and BTOR_PROXY_NODE is BTOR_NUM_OPS_NODE - 1
 * FURTHER NOTE:
 * binary nodes: [BTOR_BV_AND_NODE, ..., BTOR_LAMBDA_NODE]
 * ternary nodes: [BTOR_BCOND_NODE]
 * commutative nodes: [BTOR_BV_AND_NODE, ..., BTOR_BV_MUL_NODE]
 */
enum BtorNodeKind
{
  /* Even though the following is just for debugging purposes,
   * we should not put '#ifndef NDEBUG' around.  This would
   * make delta debugging of Heisenbugs in release mode more
   * difficult.
   */
  BTOR_INVALID_NODE   = 0,
  BTOR_CONST_NODE     = 1,
  BTOR_VAR_NODE       = 2,
  BTOR_PARAM_NODE     = 3, /* parameter for lambda expressions */
  BTOR_BV_SLICE_NODE  = 4,
  BTOR_BV_AND_NODE    = 5,
  BTOR_BV_EQ_NODE     = 6, /* equality on bit vectors */
  BTOR_FUN_EQ_NODE    = 7, /* equality on arrays */
  BTOR_BV_ADD_NODE    = 8,
  BTOR_BV_MUL_NODE    = 9,
  BTOR_BV_ULT_NODE    = 10,
  BTOR_BV_SLL_NODE    = 11,
  BTOR_BV_SRL_NODE    = 12,
  BTOR_BV_UDIV_NODE   = 13,
  BTOR_BV_UREM_NODE   = 14,
  BTOR_BV_CONCAT_NODE = 15,
  BTOR_APPLY_NODE     = 16,
  BTOR_FORALL_NODE    = 17,
  BTOR_EXISTS_NODE    = 18,
  BTOR_LAMBDA_NODE    = 19, /* lambda expression */
  BTOR_COND_NODE      = 20, /* conditional on bit vectors */
  BTOR_ARGS_NODE      = 21,
  BTOR_UF_NODE        = 22,
  BTOR_UPDATE_NODE    = 23,
  BTOR_PROXY_NODE     = 24, /* simplified expression without children */
  BTOR_NUM_OPS_NODE   = 25

  // NOTE: do not change this without changing 'g_btor_op2string' too ...
};

typedef enum BtorNodeKind BtorNodeKind;

extern const char *const g_btor_op2str[BTOR_NUM_OPS_NODE];

#define BTOR_BV_NODE_STRUCT                                                \
  struct                                                                   \
  {                                                                        \
    BtorNodeKind kind : 5;        /* kind of expression */                 \
    uint8_t constraint : 1;       /* top level constraint ? */             \
    uint8_t erased : 1;           /* for debugging purposes */             \
    uint8_t disconnected : 1;     /* for debugging purposes */             \
    uint8_t unique : 1;           /* in unique table? */                   \
    uint8_t parameterized : 1;    /* param as sub expression ? */          \
    uint8_t lambda_below : 1;     /* lambda as sub expression ? */         \
    uint8_t quantifier_below : 1; /* quantifier as sub expression ? */     \
    uint8_t apply_below : 1;      /* apply as sub expression ? */          \
    uint8_t propagated : 1;       /* is set during propagation */          \
    uint8_t is_array : 1;         /* function represents array ? */        \
    uint8_t arity : 2;            /* arity of operator (at most 3) */      \
    uint8_t bytes;                /* allocated bytes */                    \
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

struct BtorBVSliceNode
{
  BTOR_BV_NODE_STRUCT;
  BTOR_BV_ADDITIONAL_NODE_STRUCT;
  uint32_t upper;
  uint32_t lower;
};

typedef struct BtorBVSliceNode BtorBVSliceNode;

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

/*------------------------------------------------------------------------*/

static inline BtorNode *
btor_node_set_tag (BtorNode *node, uintptr_t tag)
{
  return (BtorNode *) (tag | (uintptr_t) node);
}

static inline BtorNode *
btor_node_invert (const BtorNode *node)
{
  return (BtorNode *) (1ul ^ (uintptr_t) node);
}

static inline BtorNode *
btor_node_cond_invert (const BtorNode *cond, const BtorNode *node)
{
  return (BtorNode *) (((uintptr_t) cond & 1ul) ^ (uintptr_t) node);
}

static inline bool
btor_node_is_inverted (const BtorNode *node)
{
  return (1ul & (uintptr_t) node) != 0;
}

static inline BtorNode *
btor_node_real_addr (const BtorNode *node)
{
  return (BtorNode *) (~3ul & (uintptr_t) node);
}

static inline bool
btor_node_is_regular (const BtorNode *node)
{
  return (3ul & (uintptr_t) node) == 0;
}

static inline bool
btor_node_is_synth (const BtorNode *node)
{
  return btor_node_real_addr (node)->av != 0;
}

/*------------------------------------------------------------------------*/

static inline bool
btor_node_is_unary_kind (BtorNodeKind kind)
{
  return kind == BTOR_BV_SLICE_NODE;
}

static inline bool
btor_node_is_binary_kind (BtorNodeKind kind)
{
  return kind >= BTOR_BV_AND_NODE && kind <= BTOR_LAMBDA_NODE;
}

static inline bool
btor_node_is_binary_commutative_kind (BtorNodeKind kind)
{
  return kind >= BTOR_BV_AND_NODE && kind <= BTOR_BV_MUL_NODE;
}

static inline bool
btor_node_is_ternary_kind (BtorNodeKind kind)
{
  return kind >= BTOR_COND_NODE;
}

static inline bool
btor_node_is_unary (const BtorNode *exp)
{
  assert (exp);
  return btor_node_is_unary_kind (btor_node_real_addr (exp)->kind);
}

static inline bool
btor_node_is_binary (const BtorNode *exp)
{
  assert (exp);
  return btor_node_is_binary_kind (btor_node_real_addr (exp)->kind);
}

static inline bool
btor_node_is_binary_commutative (const BtorNode *exp)
{
  assert (exp);
  return btor_node_is_binary_commutative_kind (btor_node_real_addr (exp)->kind);
}

static inline bool
btor_node_is_ternary (const BtorNode *exp)
{
  assert (exp);
  return btor_node_is_ternary_kind (btor_node_real_addr (exp)->kind);
}

static inline bool
btor_node_is_invalid (const BtorNode *exp)
{
  assert (exp);
  return btor_node_real_addr (exp)->kind == BTOR_INVALID_NODE;
}

static inline bool
btor_node_is_proxy (const BtorNode *exp)
{
  assert (exp);
  return btor_node_real_addr (exp)->kind == BTOR_PROXY_NODE;
}

static inline bool
btor_node_is_bv_const (const BtorNode *exp)
{
  assert (exp);
  exp = btor_node_real_addr (exp);
  return btor_sort_is_bv (exp->btor, exp->sort_id)
         && exp->kind == BTOR_CONST_NODE;
}

static inline bool
btor_node_is_bv_var (const BtorNode *exp)
{
  assert (exp);
  exp = btor_node_real_addr (exp);
  return btor_sort_is_bv (exp->btor, exp->sort_id)
         && exp->kind == BTOR_VAR_NODE;
}

static inline bool
btor_node_is_bv_eq (const BtorNode *exp)
{
  assert (exp);
  return btor_node_real_addr (exp)->kind == BTOR_BV_EQ_NODE;
}

static inline bool
btor_node_is_fun_eq (const BtorNode *exp)
{
  assert (exp);
  return btor_node_real_addr (exp)->kind == BTOR_FUN_EQ_NODE;
}

static inline bool
btor_node_is_bv_and (const BtorNode *exp)
{
  assert (exp);
  return btor_node_real_addr (exp)->kind == BTOR_BV_AND_NODE;
}

static inline bool
btor_node_is_bv_ult (const BtorNode *exp)
{
  assert (exp);
  return btor_node_real_addr (exp)->kind == BTOR_BV_ULT_NODE;
}

static inline bool
btor_node_is_bv_add (const BtorNode *exp)
{
  assert (exp);
  return btor_node_real_addr (exp)->kind == BTOR_BV_ADD_NODE;
}

static inline bool
btor_node_is_bv_mul (const BtorNode *exp)
{
  assert (exp);
  return btor_node_real_addr (exp)->kind == BTOR_BV_MUL_NODE;
}

static inline bool
btor_node_is_bv_udiv (const BtorNode *exp)
{
  assert (exp);
  return btor_node_real_addr (exp)->kind == BTOR_BV_UDIV_NODE;
}

static inline bool
btor_node_is_bv_urem (const BtorNode *exp)
{
  assert (exp);
  return btor_node_real_addr (exp)->kind == BTOR_BV_UREM_NODE;
}

static inline bool
btor_node_is_bv_slice (const BtorNode *exp)
{
  assert (exp);
  return btor_node_real_addr (exp)->kind == BTOR_BV_SLICE_NODE;
}

static inline bool
btor_node_is_bv_concat (const BtorNode *exp)
{
  assert (exp);
  return btor_node_real_addr (exp)->kind == BTOR_BV_CONCAT_NODE;
}

static inline bool
btor_node_is_cond (const BtorNode *exp)
{
  assert (exp);
  return btor_node_real_addr (exp)->kind == BTOR_COND_NODE;
}

bool btor_node_is_bv_cond (const BtorNode *exp);
bool btor_node_is_fun_cond (const BtorNode *exp);

static inline bool
btor_node_is_uf (const BtorNode *exp)
{
  assert (exp);
  return btor_node_real_addr (exp)->kind == BTOR_UF_NODE;
}

static inline bool
btor_node_is_array (const BtorNode *exp)
{
  assert (exp);
  return btor_node_real_addr (exp)->is_array == 1;
}

static inline bool
btor_node_is_forall (const BtorNode *exp)
{
  assert (exp);
  return btor_node_real_addr (exp)->kind == BTOR_FORALL_NODE;
}

static inline bool
btor_node_is_exists (const BtorNode *exp)
{
  assert (exp);
  return btor_node_real_addr (exp)->kind == BTOR_EXISTS_NODE;
}

static inline bool
btor_node_is_quantifier (const BtorNode *exp)
{
  return btor_node_is_forall (exp) || btor_node_is_exists (exp);
}

static inline bool
btor_node_is_lambda (const BtorNode *exp)
{
  assert (exp);
  return btor_node_real_addr (exp)->kind == BTOR_LAMBDA_NODE;
}

static inline bool
btor_node_is_binder (const BtorNode *exp)
{
  return btor_node_is_quantifier (exp) || btor_node_is_lambda (exp);
}

static inline bool
btor_node_is_update (const BtorNode *exp)
{
  assert (exp);
  return btor_node_real_addr (exp)->kind == BTOR_UPDATE_NODE;
}

static inline bool
btor_node_is_fun (const BtorNode *exp)
{
  return btor_node_is_lambda (exp) || btor_node_is_uf (exp)
         || btor_node_is_fun_cond (exp) || btor_node_is_update (exp);
}

static inline bool
btor_node_is_uf_array (const BtorNode *exp)
{
  return btor_node_is_uf (exp)
         && ((BtorUFNode *) btor_node_real_addr (exp))->is_array;
}

static inline bool
btor_node_is_param (const BtorNode *exp)
{
  assert (exp);
  return btor_node_real_addr (exp)->kind == BTOR_PARAM_NODE;
}

static inline bool
btor_node_is_args (const BtorNode *exp)
{
  assert (exp);
  return btor_node_real_addr (exp)->kind == BTOR_ARGS_NODE;
}

static inline bool
btor_node_is_apply (const BtorNode *exp)
{
  assert (exp);
  return btor_node_real_addr (exp)->kind == BTOR_APPLY_NODE;
}

static inline bool
btor_node_is_array_or_bv_eq (const BtorNode *exp)
{
  return btor_node_is_fun_eq (exp) || btor_node_is_bv_eq (exp);
}

/*------------------------------------------------------------------------*/

bool btor_node_is_bv_const_one (Btor *btor, BtorNode *exp);

bool btor_node_is_bv_const_min_signed (Btor *btor, BtorNode *exp);
bool btor_node_is_bv_const_max_signed (Btor *btor, BtorNode *exp);

bool btor_node_is_neg (Btor *btor, BtorNode *exp, BtorNode **res);

/*------------------------------------------------------------------------*/

/* Get the id of an expression (negative if exp is inverted). */
static inline int32_t
btor_node_get_id (const BtorNode *exp)
{
  assert (exp);
  return btor_node_is_inverted (exp) ? -btor_node_real_addr (exp)->id : exp->id;
}

static inline int32_t
btor_node_get_tag (const BtorNode *exp)
{
  return (int32_t) (3ul & (uintptr_t) exp);
}

/*========================================================================*/

/* Copies expression (increments reference counter). */
BtorNode *btor_node_copy (Btor *btor, BtorNode *exp);

/* Releases expression (decrements reference counter). */
void btor_node_release (Btor *btor, BtorNode *exp);

/*------------------------------------------------------------------------*/

static inline BtorSortId
btor_node_get_sort_id (const BtorNode *exp)
{
  assert (exp);
  return btor_node_real_addr (exp)->sort_id;
}

static inline void
btor_node_set_sort_id (BtorNode *exp, BtorSortId id)
{
  assert (exp);
  btor_node_real_addr (exp)->sort_id = id;
}

/*------------------------------------------------------------------------*/

void btor_node_inc_ext_ref_counter (Btor *btor, BtorNode *e);

void btor_node_dec_ext_ref_counter (Btor *btor, BtorNode *e);

/*------------------------------------------------------------------------*/

/* Convert 'exp' to a proxy expression.
 * NOTE: 'exp' must be already simplified */
void btor_node_set_to_proxy (Btor *btor, BtorNode *exp);

/*------------------------------------------------------------------------*/

/* Set parsed id (BTOR format only, needed for model output). */
void btor_node_set_btor_id (Btor *btor, BtorNode *exp, int32_t id);

/* Get parsed id (BTOR format only, needed for model output). */
int32_t btor_node_get_btor_id (BtorNode *exp);

/* Get the exp (belonging to instance 'btor') that matches given id.
 * Note: The main difference to 'btor_node_match_by_id' is that this function
 *       does NOT increase the reference counter, and passing and 'id' < 0
 *       will return an inverted node */
BtorNode *btor_node_get_by_id (Btor *btor, int32_t id);

/* Retrieve the exp (belonging to instance 'btor') that matches given id.
 * Note: increases ref counter of returned match!
 * Note: 'id' must be greater 0
 *       -> will not return a conditionally inverted node */
BtorNode *btor_node_match_by_id (Btor *btor, int32_t id);

/*------------------------------------------------------------------------*/

/* Gets the symbol of an expression. */
char *btor_node_get_symbol (Btor *btor, const BtorNode *exp);

/* Sets the symbol of an expression. */
void btor_node_set_symbol (Btor *btor, BtorNode *exp, const char *symbol);

/* Get the exp (belonging to instance 'btor') that matches given symbol.
 * Note: does NOT increase the ref counter */
BtorNode *btor_node_get_by_symbol (Btor *btor, const char *sym);

/* Retrieve the exp (belonging to instance 'btor') that matches given symbol.
 * Note: increases ref counter of returned match! */
BtorNode *btor_node_match_by_symbol (Btor *btor, const char *sym);

/*------------------------------------------------------------------------*/

/* Retrieve the exp (belonging to instance 'btor') that matches given
 * expression by id. This is intended to be used for handling expressions
 * of a cloned instance (in a clone and its parent, expressions
 * with the same id correspond to each other, i.e. initially, the cloned
 * expression is an identical copy of the parent expression).
 * (Note: increases ref counter of return match!) */
BtorNode *btor_node_match (Btor *btor, BtorNode *exp);

/*------------------------------------------------------------------------*/

/* Compares two expression pairs by ID */
int32_t btor_node_compare_by_id (const BtorNode *exp0, const BtorNode *exp1);
/* Compare function for expressions (by ID) to be used for qsort */
int32_t btor_node_compare_by_id_qsort_desc (const void *p, const void *q);
int32_t btor_node_compare_by_id_qsort_asc (const void *p, const void *q);

/* Hashes expression by ID */
uint32_t btor_node_hash_by_id (const BtorNode *exp);

/*------------------------------------------------------------------------*/

/* Get the bit width of a bit vector expression */
uint32_t btor_node_bv_get_width (Btor *btor, const BtorNode *exp);
/* Get the bit width of the array elements / function return value. */
uint32_t btor_node_fun_get_width (Btor *btor, const BtorNode *exp);
/* Get the index width of an array expression */
uint32_t btor_node_array_get_index_width (Btor *btor, const BtorNode *e_array);

/*------------------------------------------------------------------------*/

BtorBitVector *btor_node_bv_const_get_bits (BtorNode *exp);
BtorBitVector *btor_node_bv_const_get_invbits (BtorNode *exp);
void btor_node_bv_const_set_bits (BtorNode *exp, BtorBitVector *bits);
void btor_node_bv_const_set_invbits (BtorNode *exp, BtorBitVector *bits);

/*------------------------------------------------------------------------*/

/* Gets the number of arguments of lambda expression 'exp'. */
uint32_t btor_node_fun_get_arity (Btor *btor, BtorNode *exp);

/* Gets the number of arguments of an argument expression 'exp'. */
uint32_t btor_node_args_get_arity (Btor *btor, BtorNode *exp);

/*------------------------------------------------------------------------*/

BtorNode *btor_node_binder_get_body (BtorNode *binder);
void btor_node_binder_set_body (BtorNode *binder, BtorNode *body);

/*------------------------------------------------------------------------*/

BtorPtrHashTable *btor_node_lambda_get_static_rho (BtorNode *lambda);

void btor_node_lambda_set_static_rho (BtorNode *lambda,
                                      BtorPtrHashTable *static_rho);

BtorPtrHashTable *btor_node_lambda_copy_static_rho (Btor *btor,
                                                    BtorNode *lambda);

void btor_node_lambda_delete_static_rho (Btor *btor, BtorNode *lambda);

/*------------------------------------------------------------------------*/

uint32_t btor_node_bv_slice_get_upper (BtorNode *slice);
uint32_t btor_node_bv_slice_get_lower (BtorNode *slice);

/*------------------------------------------------------------------------*/

BtorNode *btor_node_param_get_binder (BtorNode *param);

void btor_node_param_set_binder (BtorNode *param, BtorNode *lambda);

bool btor_node_param_is_bound (BtorNode *param);

bool btor_node_param_is_exists_var (BtorNode *param);

bool btor_node_param_is_forall_var (BtorNode *param);

BtorNode *btor_node_param_get_assigned_exp (BtorNode *param);

BtorNode *btor_node_param_set_assigned_exp (BtorNode *param, BtorNode *exp);

/*------------------------------------------------------------------------*/

BtorNode *btor_node_create_bv_const (Btor *btor, const BtorBitVector *bits);

BtorNode *btor_node_create_var (Btor *btor,
                                BtorSortId sort,
                                const char *symbol);

BtorNode *btor_node_create_uf (Btor *btor, BtorSortId sort, const char *symbol);

BtorNode *btor_node_create_param (Btor *btor,
                                  BtorSortId sort,
                                  const char *symbol);

BtorNode *btor_node_create_bv_slice (Btor *btor,
                                     BtorNode *exp,
                                     uint32_t upper,
                                     uint32_t lower);

BtorNode *btor_node_create_bv_and (Btor *btor, BtorNode *e0, BtorNode *e1);

BtorNode *btor_node_create_eq (Btor *btor, BtorNode *e0, BtorNode *e1);

BtorNode *btor_node_create_bv_add (Btor *btor, BtorNode *e0, BtorNode *e1);

BtorNode *btor_node_create_bv_mul (Btor *btor, BtorNode *e0, BtorNode *e1);

BtorNode *btor_node_create_bv_ult (Btor *btor, BtorNode *e0, BtorNode *e1);

BtorNode *btor_node_create_bv_sll (Btor *btor, BtorNode *e0, BtorNode *e1);

BtorNode *btor_node_create_bv_srl (Btor *btor, BtorNode *e0, BtorNode *e1);

BtorNode *btor_node_create_bv_udiv (Btor *btor, BtorNode *e0, BtorNode *e1);

BtorNode *btor_node_create_bv_urem (Btor *btor, BtorNode *e0, BtorNode *e1);

BtorNode *btor_node_create_bv_concat (Btor *btor, BtorNode *e0, BtorNode *e1);

BtorNode *btor_node_create_cond (Btor *btor,
                                 BtorNode *e_cond,
                                 BtorNode *e_if,
                                 BtorNode *e_else);

BtorNode *btor_node_create_args (Btor *btor, BtorNode *args[], uint32_t argc);

BtorNode *btor_node_create_apply (Btor *btor, BtorNode *fun, BtorNode *args);

BtorNode *btor_node_create_lambda (Btor *btor, BtorNode *param, BtorNode *body);

BtorNode *btor_node_create_forall (Btor *btor, BtorNode *param, BtorNode *body);

BtorNode *btor_node_create_quantifier (Btor *btor,
                                       BtorNodeKind kind,
                                       BtorNode *param,
                                       BtorNode *body);

BtorNode *btor_node_create_exists (Btor *btor, BtorNode *param, BtorNode *body);

BtorNode *btor_node_create_update (Btor *btor,
                                   BtorNode *fun,
                                   BtorNode *args,
                                   BtorNode *value);

/*========================================================================*/

struct BtorNodePair
{
  BtorNode *node1;
  BtorNode *node2;
};

typedef struct BtorNodePair BtorNodePair;

BtorNodePair *btor_node_pair_new (Btor *, BtorNode *, BtorNode *);

void btor_node_pair_delete (Btor *, BtorNodePair *);

uint32_t btor_node_pair_hash (const BtorNodePair *);

int32_t btor_node_pair_compare (const BtorNodePair *, const BtorNodePair *);

#endif
