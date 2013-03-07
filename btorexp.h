/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2010 Robert Daniel Brummayer.
 *  Copyright (C) 2010-2012 Armin Biere.
 *  Copyright (C) 2012 Aina Niemetz, Mathias Preiner.
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
#include "btormem.h"
#include "btorqueue.h"
#include "btorstack.h"

/*------------------------------------------------------------------------*/

enum BtorSortKind
{
  BTOR_INVALID_SORT = 0,
  BTOR_BOOL_SORT    = 1,
  BTOR_BITVEC_SORT  = 2,
  BTOR_ARRAY_SORT   = 3,
  BTOR_LST_SORT     = 4,
  BTOR_FUN_SORT     = 5
};

typedef enum BtorSortKind BtorSortKind;

typedef struct BtorBitVecSort BtorBitVecSort;
typedef struct BtorArraySort BtorArraySort;
typedef struct BtorLstSort BtorLstSort;
typedef struct BtorFunSort BtorFunSort;

struct BtorBitVecSort
{
  int len;
};

struct BtorArraySort
{
  BtorSort *index;
  BtorSort *element;
};

struct BtorLstSort
{
  BtorSort *head;
  BtorSort *tail;
};

struct BtorFunSort
{
  BtorSort *domain;
  BtorSort *codomain;
};

struct BtorSort
{
  BtorSortKind kind;  // what kind of sort
  unsigned id;        // fixed id
  int refs;           // reference counter
  BtorSort *next;     // collision chain for unique table
  union
  {
    BtorBitVecSort bitvec;
    BtorArraySort array;
    BtorLstSort lst;
    BtorFunSort fun;
  };
};

struct BtorSortUniqueTable
{
  int size;
  int num_elements;
  BtorSort **chains;
};

typedef struct BtorSortUniqueTable BtorSortUniqueTable;

/*------------------------------------------------------------------------*/

BTOR_DECLARE_STACK (NodePtr, BtorNode *);

BTOR_DECLARE_QUEUE (NodePtr, BtorNode *);

/* NOTE: DO NOT REORDER THE INDICES.
 * CERTAIN MACROS DEPEND ON ORDER.
 * Some code also depends on that BTOR_INVALID_NODE, BTOR_CONST_NODE
 * and BTOR_VAR_NODE are at the beginning,
 * and BTOR_PROXY_NODE is BTOR_NUM_OPS_NODE - 1
 * FURTHER NOTE:
 * binary nodes: [BTOR_AND_NODE, ..., BTOR_LAMBDA_NODE]
 * ternary nodes: [BTOR_WRITE_NODE, ..., BTOR_ACOND_NODE]
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
  BTOR_READ_NODE      = 17,
  BTOR_LAMBDA_NODE    = 18, /* lambda expression */
  BTOR_WRITE_NODE     = 19,
  BTOR_BCOND_NODE     = 20, /* conditional on bit vectors */
  BTOR_ACOND_NODE     = 21, /* conditional on arrays */
  BTOR_PROXY_NODE     = 22, /* simplified expression without children */
  BTOR_NUM_OPS_NODE   = 23
};

typedef enum BtorNodeKind BtorNodeKind;

typedef struct BtorNodePair BtorNodePair;

#define BTOR_BV_VAR_NODE_STRUCT                                         \
  struct                                                                \
  {                                                                     \
    BtorNodeKind kind : 5;          /* kind of expression */            \
    unsigned int mark : 3;          /* for DAG traversal */             \
    unsigned int aux_mark : 2;      /* auxiliary mark flag */           \
    unsigned int array_mark : 1;    /* for bottom up array traversal */ \
    unsigned int beta_mark : 1;     /* mark for beta_reduce */          \
    unsigned int eval_mark : 2;     /* mark for eval_exp */             \
    unsigned int synth_mark : 2;    /* mark for synthesize_exp */       \
    unsigned int reachable : 1;     /* reachable from root ? */         \
    unsigned int tseitin : 1;       /* tseitin encoded into SAT ? */    \
    unsigned int vread : 1;         /* virtual read ? */                \
    unsigned int vread_index : 1;   /* index for two virtual reads ? */ \
    unsigned int constraint : 1;    /* top level constraint ? */        \
    unsigned int erased : 1;        /* for debugging purposes */        \
    unsigned int disconnected : 1;  /* for debugging purposes */        \
    unsigned int unique : 1;        /* in unique table? */              \
    unsigned int bytes : 8;         /* allocated bytes */               \
    unsigned int arity : 2;         /* arity of operator */             \
    unsigned int parameterized : 1; /* param as sub expression ? */     \
    unsigned int lambda_below : 1;  /* lambda as sub expression ? */    \
    char *bits;                     /* three-valued bits */             \
    int id;                         /* unique expression id */          \
    int len;                        /* number of bits */                \
    int refs;                       /* reference counter */             \
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

#define BTOR_BV_ADDITIONAL_NODE_STRUCT                                  \
  struct                                                                \
  {                                                                     \
    union                                                               \
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
      BtorNode *e[3]; /* three expression children */                   \
    };                                                                  \
    BtorNode *prev_parent[3]; /* prev in parent list of child i */      \
    BtorNode *next_parent[3]; /* next in parent list of child i */      \
  }

#define BTOR_ARRAY_VAR_NODE_STRUCT                                           \
  struct                                                                     \
  {                                                                          \
    int index_len;                    /* length of the index */              \
    BtorNode *first_aeq_acond_parent; /* first array equality or array       \
                                               conditional in parent list */ \
    BtorNode *last_aeq_acond_parent;  /* last array equality or array        \
                                               conditional in parent list */ \
  }

#define BTOR_ARRAY_ADDITIONAL_NODE_STRUCT                                  \
  struct                                                                   \
  {                                                                        \
    BtorNode *prev_aeq_acond_parent[3]; /* prev array equality or          \
                                                 conditional in aeq acond  \
                                                 parent list of child i */ \
    BtorNode *next_aeq_acond_parent[3]; /* next array equality or          \
                                                 conditional in aeq acond  \
                                                 parent list of child i */ \
  }

struct BtorBVVarNode
{
  BTOR_BV_VAR_NODE_STRUCT;
  char *symbol;
};

typedef struct BtorBVVarNode BtorBVVarNode;

struct BtorParamNode
{
  BTOR_BV_VAR_NODE_STRUCT;
  char *symbol;
  BtorNode *lambda_exp;          /* 1:1 relation param:lambda_exp */
  BtorNodePtrStack assigned_exp; /* scoped assigned expression stack */
  // BtorNode *assigned_exp;   /* is assigned before beta-reduction */
};

typedef struct BtorParamNode BtorParamNode;

struct BtorBVConstNode
{
  BTOR_BV_VAR_NODE_STRUCT;
};

typedef struct BtorBVConstNode BtorBVConstNode;

struct BtorBVNode
{
  BTOR_BV_VAR_NODE_STRUCT;
  BTOR_BV_ADDITIONAL_NODE_STRUCT;
};

typedef struct BtorBVNode BtorBVNode;

struct BtorArrayVarNode
{
  BTOR_BV_VAR_NODE_STRUCT;
  BTOR_BV_ADDITIONAL_NODE_STRUCT;
  BTOR_ARRAY_VAR_NODE_STRUCT;
};

typedef struct BtorArrayVarNode BtorArrayVarNode;

struct BtorNode
{
  BTOR_BV_VAR_NODE_STRUCT;
  BTOR_BV_ADDITIONAL_NODE_STRUCT;
  BTOR_ARRAY_VAR_NODE_STRUCT;
  BTOR_ARRAY_ADDITIONAL_NODE_STRUCT;
};

struct BtorLambdaNode
{
  BTOR_BV_VAR_NODE_STRUCT;
  BTOR_BV_ADDITIONAL_NODE_STRUCT;
  BTOR_ARRAY_VAR_NODE_STRUCT;
  BTOR_ARRAY_ADDITIONAL_NODE_STRUCT;
  BtorPtrHashTable *synth_reads;
  int chain_depth;
};

typedef struct BtorLambdaNode BtorLambdaNode;

struct BtorNodeUniqueTable
{
  int size;
  int num_elements;
  BtorNode **chains;
};

typedef struct BtorNodeUniqueTable BtorNodeUniqueTable;

struct ConstraintStats
{
  int varsubst;
  int embedded;
  int unsynthesized;
  int synthesized;
};

typedef struct ConstraintStats ConstraintStats;

enum BtorUAMode
{
  BTOR_UA_GLOBAL_MODE = 0,
  BTOR_UA_LOCAL_MODE,
  BTOR_UA_LOCAL_INDIVIDUAL_MODE
};

typedef enum BtorUAMode BtorUAMode;

enum BtorUARef
{
  BTOR_UA_REF_BY_DOUBLING = 0,
  BTOR_UA_REF_BY_INC_ONE
};

typedef enum BtorUARef BtorUARef;

enum BtorUAEnc
{
  BTOR_UA_ENC_SIGN_EXTEND = 0,
  BTOR_UA_ENC_ZERO_EXTEND,
  BTOR_UA_ENC_ONE_EXTEND,
  BTOR_UA_ENC_EQ_CLASSES
};

typedef enum BtorUAEnc BtorUAEnc;

struct Btor
{
  BtorMemMgr *mm;
  BtorNodePtrStack nodes_id_table;
  BtorNodeUniqueTable nodes_unique_table;
  BtorSortUniqueTable sorts_unique_table;
  BtorAIGVecMgr *avmgr;
  BtorPtrHashTable *bv_vars;
  BtorPtrHashTable *array_vars;
  BtorPtrHashTable *lambdas;
  BtorNode *true_exp;
  int bv_lambda_id;    /* counter for lambda bv variables (subst) */
  int array_lambda_id; /* counter for lambda array variables (subst) */
  int rec_rw_calls;    /* calls for recursive rewriting */
  int rec_read_acond_calls;
  int valid_assignments;
  int rewrite_level;
  int verbosity;
#ifndef NBTORLOG
  int loglevel;
#endif
  int vis_idx; /* file index for visualizing expressions */
  int vread_index_id;
  int inconsistent;
  int model_gen;            /* model generation enabled */
  int external_refs;        /* external references (library mode) */
  int inc_enabled;          /* incremental usage enabled ? */
  int btor_sat_btor_called; /* how often is btor_sat_btor been called */
  int msgtick;              /* message tick in incremental mode */
  int rewrite_writes;       /* rewrite writes to lambda expressions */
  int rewrite_reads;        /* rewrite reads on lambda expressions */
  int pprint;               /* reindex exps when dumping */

  BtorPtrHashTable *exp_pair_eq_table;
  BtorPtrHashTable *exp_pair_and_table;

  BtorPtrHashTable *varsubst_constraints;
  BtorPtrHashTable *embedded_constraints;
  BtorPtrHashTable *unsynthesized_constraints;
  BtorPtrHashTable *synthesized_constraints;
  BtorPtrHashTable *assumptions;
  BtorPtrHashTable *var_rhs;   /* only for model generation */
  BtorPtrHashTable *array_rhs; /* only for model generation */
  BtorNodePtrStack arrays_with_model;
  BtorPtrHashTable *cache;
  /* statistics */
  int ops[BTOR_NUM_OPS_NODE];
  struct
  {
    int max_rec_rw_calls; /* maximum number of recursive rewrite calls */
    int lod_refinements;  /* number of lemmas on demand refinements */
    int synthesis_assignment_inconsistencies; /* number of restarts as a
                                                 result of lazy synthesis */
    int array_axiom_1_conflicts; /* number of array axiom 1 conflicts:
                                    a = b /\ i = j => read(a, i) = read(b, j) */
    int array_axiom_2_conflicts; /* array axiom 2 confs:
                                    i = j => read(write(a, i, e), j) = e */
    int var_substitutions;       /* number substituted vars (non array) */
    int array_substitutions;     /* num substituted array vars */
    int ec_substitutions;        /* embedded constraint substitutions */
    int vreads;                  /* number of virtual reads */
    int linear_equations;        /* number of linear equations */
    int gaussian_eliminations;   /* number of gaussian eliminations */
    int eliminated_slices;       /* number of eliminated slices */
    int skeleton_constraints;    /* number of extracted skeleton constraints */
    int adds_normalized;         /* number of add chains normalizations */
    int muls_normalized;         /* number of mul chains normalizations */
    int read_props_construct;    /* how often have we pushed a read over
                                    write during construction */
    long long int lemmas_size_sum;  /* sum of the size of all added lemmas */
    long long int lclause_size_sum; /* sum of the size of all linking clauses */
    ConstraintStats constraints, oldconstraints;
    long long expressions;
    long long beta_reduce_calls;
    long long eval_exp_calls;
    long long lambda_synth_reads;
    long long lambda_chains_merged;
    long long lambdas_merged;
  } stats;

  struct
  {
    double rewrite;
    double sat;
    double subst;
    double embedded;
    double slicing;
    double skel;
    double beta;
    double eval;
  } time;
};

#define BTOR_IS_BV_CONST_NODE_KIND(kind) ((kind) == BTOR_BV_CONST_NODE)

#define BTOR_IS_BV_VAR_NODE_KIND(kind) ((kind) == BTOR_BV_VAR_NODE)

#define BTOR_IS_ARRAY_VAR_NODE_KIND(kind) (kind == BTOR_ARRAY_VAR_NODE)

#define BTOR_IS_PARAM_NODE_KIND(kind) ((kind) == BTOR_PARAM_NODE)

#define BTOR_IS_BV_EQ_NODE_KIND(kind) (kind == BTOR_BEQ_NODE)

#define BTOR_IS_ARRAY_EQ_NODE_KIND(kind) (kind == BTOR_AEQ_NODE)

#define BTOR_IS_READ_NODE_KIND(kind) (kind == BTOR_READ_NODE)

#define BTOR_IS_LAMBDA_NODE_KIND(kind) ((kind) == BTOR_LAMBDA_NODE)

#define BTOR_IS_WRITE_NODE_KIND(kind) (kind == BTOR_WRITE_NODE)

#define BTOR_IS_ARRAY_COND_NODE_KIND(kind) (kind == BTOR_ACOND_NODE)

#define BTOR_IS_BV_COND_NODE_KIND(kind) (kind == BTOR_BCOND_NODE)

#define BTOR_IS_PROXY_NODE_KIND(kind) ((kind) == BTOR_PROXY_NODE)

/* array nodes: array var, write, acond, lambda
 *		proxy (if it was originally one of the above) */
#define BTOR_IS_ARRAY_NODE_KIND(kind)                             \
  (((kind) == BTOR_ARRAY_VAR_NODE) || ((kind) == BTOR_WRITE_NODE) \
   || ((kind) == BTOR_ACOND_NODE) || ((kind) == BTOR_LAMBDA_NODE))

#define BTOR_IS_UNARY_NODE_KIND(kind) ((kind) == BTOR_SLICE_NODE)

#define BTOR_IS_BINARY_NODE_KIND(kind) \
  ((((kind) >= BTOR_AND_NODE) && ((kind) <= BTOR_LAMBDA_NODE)))

#define BTOR_IS_BINARY_COMMUTATIVE_NODE_KIND(kind) \
  (((kind) >= BTOR_AND_NODE) && ((kind) <= BTOR_MUL_NODE))

#define BTOR_IS_TERNARY_NODE_KIND(kind) \
  (((kind) >= BTOR_WRITE_NODE) && ((kind) <= BTOR_ACOND_NODE))

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
  ((exp) && (BTOR_IS_ARRAY_EQ_NODE (exp) || BTOR_IS_BV_EQ_NODE (exp)))

#define BTOR_IS_READ_NODE(exp) ((exp) && BTOR_IS_READ_NODE_KIND ((exp)->kind))

#define BTOR_IS_LAMBDA_NODE(exp) \
  ((exp) && BTOR_IS_LAMBDA_NODE_KIND ((exp)->kind))

#define BTOR_IS_WRITE_NODE(exp) ((exp) && BTOR_IS_WRITE_NODE_KIND ((exp)->kind))

#define BTOR_IS_ARRAY_COND_NODE(exp) \
  ((exp) && BTOR_IS_ARRAY_COND_NODE_KIND ((exp)->kind))

#define BTOR_IS_BV_COND_NODE(exp) \
  ((exp) && BTOR_IS_BV_COND_NODE_KIND ((exp)->kind))

#define BTOR_IS_ARRAY_OR_BV_COND_NODE(exp) \
  ((exp) && (BTOR_IS_ARRAY_COND_NODE (exp) || BTOR_IS_BV_COND_NODE (exp)))

#define BTOR_IS_PROXY_NODE(exp) ((exp) && BTOR_IS_PROXY_NODE_KIND ((exp)->kind))

#define BTOR_IS_ARRAY_NODE(exp) \
  ((exp) && (BTOR_IS_ARRAY_NODE_KIND ((exp)->kind)))

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

#define BTOR_IS_ACC_NODE(exp) \
  (BTOR_IS_READ_NODE (exp) || BTOR_IS_WRITE_NODE (exp))

#define BTOR_GET_INDEX_ACC_NODE(exp) ((exp)->e[1])

#define BTOR_GET_VALUE_ACC_NODE(exp) \
  (BTOR_IS_READ_NODE (exp) ? (exp) : (exp)->e[2])

#define BTOR_ACC_TARGET_NODE(exp) \
  (BTOR_IS_READ_NODE (exp) ? (exp)->e[0] : (exp))

#define BTOR_IS_SYNTH_NODE(exp) ((exp)->av != 0)

/*------------------------------------------------------------------------*/

/* Creates new boolector instance. */
Btor *btor_new_btor (void);

/* Clone an existing boolector instance. */
Btor *btor_clone_btor (Btor *);

/* Sets rewrite level [0,2]. */
void btor_set_rewrite_level_btor (Btor *btor, int rewrite_level);

/* Enable rewriting of writes to lambda expressions. */
void btor_enable_rewrite_writes (Btor *btor);

/* Enable rewriting of reads on lambda expressions. */
void btor_enable_rewrite_reads (Btor *btor);

/* Disable pretty printing when dumping and rewriting of writes is enabled.  */
void btor_disable_pretty_print (Btor *btor);

/* Enables model generation. */
void btor_enable_model_gen (Btor *btor);

/* Enables incremental usage which means that assumptions are enabled
 * and btor_sat_btor can be called more than once. Note that enabling this
 * feature turns off some optimizations which are not possible anymore.
 */
void btor_enable_inc_usage (Btor *btor);

int btor_set_sat_solver (Btor *, const char *);

/* Sets verbosity [-1,3] of btor and all sub-components
 * if verbosity is set to -1, then boolector is in "quiet mode" and
 * does not print any output.
 */
void btor_set_verbosity_btor (Btor *btor, int verbosity);

/* Set log level.
 */
#ifndef NBTORLOG
void btor_set_loglevel_btor (Btor *btor, int loglevel);
#endif

/* Deletes boolector. */
void btor_delete_btor (Btor *btor);

/* Gets version. */
const char *btor_version (Btor *btor);

/* Prints statistics. */
void btor_print_stats_btor (Btor *btor);

/*------------------------------------------------------------------------*/

BtorSort *btor_bool_sort (Btor *btor);

BtorSort *btor_bitvec_sort (Btor *btor, int len);

BtorSort *btor_array_sort (Btor *btor, BtorSort *idx, BtorSort *elem);

BtorSort *btor_lst_sort (Btor *btor, BtorSort *head, BtorSort *tail);

BtorSort *btor_fun_sort (Btor *btor, BtorSort *dom, BtorSort *codom);

BtorSort *btor_copy_sort (Btor *btor, BtorSort *sort);

void btor_release_sort (Btor *btor, BtorSort *sort);

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
BtorNode *btor_unsigned_to_exp (Btor *btor, unsigned u, int len);

/* Binary constant representing the signed integer.
 * The constant is obtained by either truncating bits
 * or by signed extension (padding with ones).
 * len > 0
 */
BtorNode *btor_int_to_exp (Btor *emg, int i, int len);

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

/* Apply node that applies 'args' to 'lambda'.
 */
BtorNode *btor_apply_exp (Btor *btor,
                          int argc,
                          BtorNode **args,
                          BtorNode *lambda);

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

/* Apply 'args' to parameters of lambdas and reduce 'lambda' */
BtorNode *btor_apply_and_reduce (Btor *btor,
                                 int argc,
                                 BtorNode **args,
                                 BtorNode *lambda);

/* Beta reduce 'exp' */
BtorNode *btor_reduce (Btor *btor, BtorNode *exp);

/* Gets the length of an expression representing the number of bits. */
int btor_get_exp_len (Btor *btor, BtorNode *exp);

/* Determines if expression is an array or not. */
int btor_is_array_exp (Btor *btor, BtorNode *exp);

/* Gets the number of bits used by indices on 'e_array'. */
int btor_get_index_exp_len (Btor *btor, BtorNode *e_array);

/* Gets the symbol of a variable. */
char *btor_get_symbol_exp (Btor *btor, BtorNode *exp);

/* Determines if expression is a param or not. */
int btor_is_param_exp (Btor *btor, BtorNode *exp);

/* Determines if param is already bound to a lambda expression or not. */
int btor_is_bound_param (Btor *btor, BtorNode *param);

/* Determines if expression is a lambda or not. */
int btor_is_lambda_exp (Btor *btor, BtorNode *exp);

/* Copies expression (increments reference counter). */
BtorNode *btor_copy_exp (Btor *btor, BtorNode *exp);

/* Releases expression (decrements reference counter). */
void btor_release_exp (Btor *btor, BtorNode *exp);

/* Dumps expression(s) to file in BTOR format. */
void btor_dump_exp (Btor *btor, FILE *file, BtorNode *root);
void btor_dump_exps (Btor *btor, FILE *file, BtorNode **exps, int nroots);
void btor_dump_exps_after_global_rewriting (Btor *btor, FILE *file);

/* Dumps expression to file in SMT format.
 * format==1 || format==2
 */
void btor_dump_smt (Btor *btor, int format, FILE *file, BtorNode *root);

/* Adds top level constraint. */
void btor_add_constraint_exp (Btor *btor, BtorNode *exp);

/* Adds assumption. */
void btor_add_assumption_exp (Btor *btor, BtorNode *exp);

/* Solves SAT instance.
 */
int btor_sat_btor (Btor *btor);

/* Builds current assignment string of expression (in the SAT case)
 * and returns it.
 * Do not call before calling btor_sat_exp.
 * strlen(result) = len(exp)
 */
char *btor_bv_assignment_exp (Btor *btor, BtorNode *exp);

void btor_array_assignment_exp (
    Btor *btor, BtorNode *exp, char ***indices, char ***values, int *size);

/* Frees BV assignment obtained by calling 'btor_assignment_exp' */
void btor_free_bv_assignment_exp (Btor *btor, char *assignment);

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

/*------------------------------------------------------------------------*/

/* Synthesizes expression of arbitrary length to an AIG vector. Adds string
 * back annotation to the hash table, if the hash table is a non zero ptr.
 * The strings in 'data.asStr' are owned by the caller.  The hash table
 * is a map from AIG variables to strings.
 */
BtorAIGVec *btor_exp_to_aigvec (Btor *btor,
                                BtorNode *exp,
                                BtorPtrHashTable *table);

/* Compares two expression pairs by ID */
int btor_compare_exp_by_id (BtorNode *exp0, BtorNode *exp1);

/* Hashes expression by ID */
unsigned int btor_hash_exp_by_id (BtorNode *exp);

/* Finds most simplified expression and shortens path to it */
BtorNode *btor_simplify_exp (Btor *btor, BtorNode *exp);

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
