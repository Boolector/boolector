#ifndef BTOREXP_H_INCLUDED
#define BTOREXP_H_INCLUDED

#include "btoraigvec.h"
#include "btorhash.h"
#include "btormem.h"
#include "btorqueue.h"
#include "btorstack.h"

/*------------------------------------------------------------------------*/
/* PRIVATE INTERFACE                                                      */
/*------------------------------------------------------------------------*/

/*------------------------------------------------------------------------*/
/* Declarations                                                           */
/*------------------------------------------------------------------------*/

typedef struct BtorExp BtorExp;

typedef struct Btor Btor;

BTOR_DECLARE_STACK (ExpPtr, BtorExp *);

BTOR_DECLARE_QUEUE (ExpPtr, BtorExp *);

/* NOTE: DO NOT REORDER THE INDICES.
 * CERTAIN MACROS DEPEND ON ORDER.
 * Some code also depends on that BTOR_INVALID_EXP, BTOR_CONST_EXP
 * and BTOR_VAR_EXP are at the beginning,
 * and BTOR_PROXY_EXP is BTOR_NUM_OPS_EXP - 1
 */
enum BtorExpKind
{
  /* Even though the following is just for debugging purposes,
   * we should not put '#ifndef NDEBUG' around.  This would
   * make delta debugging of Heisenbugs in release mode more
   * difficult.
   */
  BTOR_INVALID_EXP = 0,

  BTOR_CONST_EXP  = 1,
  BTOR_VAR_EXP    = 2,
  BTOR_ARRAY_EXP  = 3,
  BTOR_SLICE_EXP  = 4,
  BTOR_AND_EXP    = 5,
  BTOR_BEQ_EXP    = 6, /* equality on bit vectors */
  BTOR_AEQ_EXP    = 7, /* equality on arrays */
  BTOR_ADD_EXP    = 8,
  BTOR_MUL_EXP    = 9,
  BTOR_ULT_EXP    = 10,
  BTOR_SLL_EXP    = 11,
  BTOR_SRL_EXP    = 12,
  BTOR_UDIV_EXP   = 13,
  BTOR_UREM_EXP   = 14,
  BTOR_CONCAT_EXP = 15,
  BTOR_READ_EXP   = 16,
  BTOR_WRITE_EXP  = 17,
  BTOR_BCOND_EXP  = 18, /* conditional on bit vectors */
  BTOR_ACOND_EXP  = 19, /* conditional on arrays */
  BTOR_PROXY_EXP  = 20, /* simplified expression without children */
};

typedef enum BtorExpKind BtorExpKind;

#define BTOR_NUM_OPS_EXP 21

typedef struct BtorExpPair BtorExpPair;

#define BTOR_BV_VAR_EXP                                                        \
  struct                                                                       \
  {                                                                            \
    BtorExpKind kind : 5;        /* kind of expression */                      \
    unsigned int mark : 3;       /* for DAG traversal */                       \
    unsigned int array_mark : 2; /* for bottom up array traversal */           \
    unsigned int aux_mark : 2;   /* auxiallary mark flag */                    \
    unsigned int synth_mark : 2; /* mark for synthesize_exp */                 \
    unsigned int reachable : 1;  /* flag determines if expression              \
                                    is reachable from root */                  \
    unsigned int                                                               \
        sat_both_phases : 1;       /* flag determines if expression has been   \
                                      encoded into SAT in both phases */       \
    unsigned int vread : 1;        /* flag determines if expression            \
                                      is a virtual read */                     \
    unsigned int vread_index : 1;  /* flat determines if expression            \
                                      is an index used by two virtual reads */ \
    unsigned int constraint : 1;   /* flag determines if expression is a       \
                                      top level constraint */                  \
    unsigned int erased : 1;       /* for debugging purposes */                \
    unsigned int disconnected : 1; /* for debugging purposes */                \
    unsigned int unique : 1;       /* in unique table? */                      \
    unsigned int bytes : 8;        /* allocated bytes */                       \
    unsigned int arity : 2;        /* arity of operator */                     \
    char *bits;                    /* three valued bits */                     \
    int id;                        /* unique expression id */                  \
    int len;                       /* number of bits */                        \
    int refs;                      /* reference counter */                     \
    union                                                                      \
    {                                                                          \
      BtorAIGVec *av;        /* synthesized AIG vector */                      \
      BtorPtrHashTable *rho; /* used for finding array conflicts */            \
    };                                                                         \
    struct BtorExp *next;         /* next element in unique table */           \
    struct BtorExp *parent;       /* parent pointer for BFS */                 \
    struct BtorExp *simplified;   /* equivalent simplified expression */       \
    Btor *btor;                   /* boolector */                              \
    struct BtorExp *first_parent; /* head of parent list */                    \
    struct BtorExp *last_parent;  /* tail of parent list */                    \
  }

#define BTOR_BV_ADDITIONAL_EXP                                               \
  struct                                                                     \
  {                                                                          \
    union                                                                    \
    {                                                                        \
      struct                                                                 \
      {                                                                      \
        char *symbol; /* symbol for output */                                \
        int upper;    /* upper index for slices */                           \
        union                                                                \
        {                                                                    \
          int lower;           /* lower index for slices */                  \
          BtorExpPair *vreads; /* virtual reads for array equalites */       \
        };                                                                   \
      };                                                                     \
      struct BtorExp *e[3]; /* three expression children */                  \
    };                                                                       \
    struct BtorExp *prev_parent[3]; /* prev exp in parent list of child i */ \
    struct BtorExp *next_parent[3]; /* next exp in parent list of child i */ \
  }

#define BTOR_ARRAY_VAR_EXP                                                   \
  struct                                                                     \
  {                                                                          \
    int index_len;                          /* length of the index */        \
    struct BtorExp *first_aeq_acond_parent; /* first array equality or array \
                                               conditional in parent list */ \
    struct BtorExp *last_aeq_acond_parent;  /* last array equality or array  \
                                               conditional in parent list */ \
  }

#define BTOR_ARRAY_ADDITIONAL_EXP                                          \
  struct                                                                   \
  {                                                                        \
    struct BtorExp *prev_aeq_acond_parent[3]; /* prev array equality or    \
                                                 conditional in aeq acond  \
                                                 parent list of child i */ \
    struct BtorExp *next_aeq_acond_parent[3]; /* next array equality or    \
                                                 conditional in aeq acond  \
                                                 parent list of child i */ \
  }

struct BtorBVVarExp
{
  BTOR_BV_VAR_EXP;
  char *symbol;
};

typedef struct BtorBVVarExp BtorBVVarExp;

struct BtorBVConstExp
{
  BTOR_BV_VAR_EXP;
};

typedef struct BtorBVConstExp BtorBVConstExp;

struct BtorBVExp
{
  BTOR_BV_VAR_EXP;
  BTOR_BV_ADDITIONAL_EXP;
};

typedef struct BtorBVExp BtorBVExp;

struct BtorArrayVarExp
{
  BTOR_BV_VAR_EXP;
  BTOR_BV_ADDITIONAL_EXP;
  BTOR_ARRAY_VAR_EXP;
};

typedef struct BtorArrayVarExp BtorArrayVarExp;

struct BtorExp
{
  BTOR_BV_VAR_EXP;
  BTOR_BV_ADDITIONAL_EXP;
  BTOR_ARRAY_VAR_EXP;
  BTOR_ARRAY_ADDITIONAL_EXP;
};

struct BtorExpUniqueTable
{
  int size;
  int num_elements;
  struct BtorExp **chains;
};

typedef struct BtorExpUniqueTable BtorExpUniqueTable;

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
  BtorExpUniqueTable table;
  BtorAIGVecMgr *avmgr;
  BtorPtrHashTable *arrays;
  int id;        /* expression id counter */
  int lambda_id; /* counter for lambda variables (subst) */
  int valid_assignments;
  int rewrite_level;
  int verbosity;
  int replay;
  int vread_index_id;
  int inconsistent;
  int model_gen;
  int external_refs;
  int assumption_usage;     /* are assumptions used ? */
  int stand_alone_mode;     /* btor_sat_btor can only be called once */
  int btor_sat_btor_called; /* how often is btor_sat_btor been called */
  int bvsce;                /* QF_BV with slice, concat and eq */
  struct                    /* Under-approximation UA */
  {
    int enabled;                     /* UA enabled */
    BtorUAMode mode;                 /* UA mode */
    BtorUARef ref;                   /* UA refinement strategy */
    BtorUAEnc enc;                   /* UA encoding strategy */
    int initial_eff_width;           /* UA initial effective bit-width */
    int global_eff_width;            /* global effective bit-width  */
    int global_max_eff_width;        /* maximum necessary effective bit-width */
    int global_last_e;               /* last global UA e for CNF */
    BtorPtrHashTable *vars_reads;    /* bv variables and reads */
    BtorPtrHashTable *writes_aconds; /* array writes and array conds */
  } ua;
  BtorPtrHashTable *exp_pair_cnf_diff_id_table; /* hash table for CNF ids */
  BtorPtrHashTable *exp_pair_cnf_eq_id_table;   /* hash table for CNF ids */
  BtorPtrHashTable *exp_pair_ass_unequal_table; /* assignment unequal */
  BtorPtrHashTable *varsubst_constraints;
  BtorPtrHashTable *embedded_constraints;
  BtorPtrHashTable *unsynthesized_constraints;
  BtorPtrHashTable *synthesized_constraints;
  BtorPtrHashTable *assumptions;
  BtorPtrHashTable *var_rhs; /* only for model generation */
  BtorExpPtrStack arrays_with_model;
  BtorExpPtrStack replay_constraints;
  /* statistics */
  int ops[BTOR_NUM_OPS_EXP];
  struct
  {
    /* number of under-approximation refinements */
    int ua_refinements;
    /* number of lemmas on demand refinements */
    int lod_refinements;
    /* number of restarts as a result of lazy synthesis */
    int synthesis_assignment_inconsistencies;
    /* number of array axiom 1 conflicts:
     * a = b /\ i = j => read(a, i) = read(b, j) */
    int array_axiom_1_conflicts;
    /* number of array axiom 2 conflicts:
     * i = j => read(write(a, i, e), j) = e */
    int array_axiom_2_conflicts;
    /* number of variables that have been substituted */
    int var_substitutions;
    /* number of array variables that have been substituted */
    int array_substitutions;
    /* embedded constraint substitutions */
    int ec_substitutions;
    /* number of virtual reads */
    int vreads;
    /* number of linear equations */
    int linear_equations;
    /* number of add chains normalizations */
    int adds_normalized;
    /* number of mul chains normalizations */
    int muls_normalized;
    /*  how often have we pushed a read over write during construction */
    int read_props_construct;
    /* sum of the size of all added lemmas */
    long long int lemmas_size_sum;
    /* sum of the size of all linking clauses */
    long long int lclause_size_sum;
    /* constraint statistics */
    ConstraintStats constraints;
    struct
    {
      ConstraintStats constraints;
    } old;
    long long expressions;
  } stats;
};

#define BTOR_IS_CONST_EXP_KIND(kind) ((kind) == BTOR_CONST_EXP)
#define BTOR_IS_VAR_EXP_KIND(kind) ((kind) == BTOR_VAR_EXP)
#define BTOR_IS_READ_EXP_KIND(kind) (kind == BTOR_READ_EXP)
#define BTOR_IS_WRITE_EXP_KIND(kind) (kind == BTOR_WRITE_EXP)
#define BTOR_IS_ARRAY_COND_EXP_KIND(kind) (kind == BTOR_ACOND_EXP)
#define BTOR_IS_PROXY_EXP_KIND(kind) ((kind) == BTOR_PROXY_EXP)
#define BTOR_IS_BV_COND_EXP_KIND(kind) (kind == BTOR_BCOND_EXP)
#define BTOR_IS_ATOMIC_ARRAY_EXP_KIND(kind) (kind == BTOR_ARRAY_EXP)
#define BTOR_IS_ARRAY_EXP_KIND(kind)                        \
  (((kind) == BTOR_ARRAY_EXP) || ((kind) == BTOR_WRITE_EXP) \
   || ((kind) == BTOR_ACOND_EXP))
#define BTOR_IS_ARRAY_EQ_EXP_KIND(kind) (kind == BTOR_AEQ_EXP)
#define BTOR_IS_BV_EQ_EXP_KIND(kind) (kind == BTOR_BEQ_EXP)
#define BTOR_IS_UNARY_EXP_KIND(kind) ((kind) == BTOR_SLICE_EXP)
#define BTOR_IS_BINARY_EXP_KIND(kind) \
  (((kind) >= BTOR_AND_EXP) && ((kind) <= BTOR_READ_EXP))
#define BTOR_IS_BINARY_COMMUTATIVE_EXP_KIND(kind) \
  (((kind) >= BTOR_AND_EXP) && ((kind) <= BTOR_MUL_EXP))
#define BTOR_IS_TERNARY_EXP_KIND(kind) \
  (((kind) >= BTOR_WRITE_EXP) && ((kind) <= BTOR_ACOND_EXP))

#define BTOR_IS_CONST_EXP(exp) (BTOR_IS_CONST_EXP_KIND ((exp)->kind))
#define BTOR_IS_VAR_EXP(exp) (BTOR_IS_VAR_EXP_KIND ((exp)->kind))
#define BTOR_IS_READ_EXP(exp) (BTOR_IS_READ_EXP_KIND ((exp)->kind))
#define BTOR_IS_WRITE_EXP(exp) (BTOR_IS_WRITE_EXP_KIND ((exp)->kind))
#define BTOR_IS_ARRAY_COND_EXP(exp) (BTOR_IS_ARRAY_COND_EXP_KIND ((exp)->kind))
#define BTOR_IS_BV_COND_EXP(exp) (BTOR_IS_BV_COND_EXP_KIND ((exp)->kind))
#define BTOR_IS_PROXY_EXP(exp) (BTOR_IS_PROXY_EXP_KIND ((exp)->kind))
#define BTOR_IS_ARRAY_OR_BV_COND_EXP(exp) \
  (BTOR_IS_ARRAY_COND_EXP (exp) || BTOR_IS_BV_COND_EXP (exp))
#define BTOR_IS_ATOMIC_ARRAY_EXP(exp) \
  (BTOR_IS_ATOMIC_ARRAY_EXP_KIND ((exp)->kind))
#define BTOR_IS_ARRAY_EXP(exp) (BTOR_IS_ARRAY_EXP_KIND ((exp)->kind))
#define BTOR_IS_ARRAY_EQ_EXP(exp) (BTOR_IS_ARRAY_EQ_EXP_KIND ((exp)->kind))
#define BTOR_IS_BV_EQ_EXP(exp) (BTOR_IS_BV_EQ_EXP_KIND ((exp)->kind))
#define BTOR_IS_ARRAY_OR_BV_EQ_EXP(exp) \
  (BTOR_IS_ARRAY_EQ_EXP (exp) || BTOR_IS_BV_EQ_EXP (exp))
#define BTOR_IS_UNARY_EXP(exp) (BTOR_IS_UNARY_EXP_KIND ((exp)->kind))
#define BTOR_IS_BINARY_EXP(exp) (BTOR_IS_BINARY_EXP_KIND ((exp)->kind))
#define BTOR_IS_TERNARY_EXP(exp) (BTOR_IS_TERNARY_EXP_KIND ((exp)->kind))

#define BTOR_INVERT_EXP(exp) ((BtorExp *) (1ul ^ (unsigned long int) (exp)))
#define BTOR_IS_INVERTED_EXP(exp) (1ul & (unsigned long int) (exp))
#define BTOR_COND_INVERT_EXP(cond_exp, exp)           \
  ((BtorExp *) (((unsigned long int) (cond_exp) &1ul) \
                ^ (unsigned long int) (exp)))
#define BTOR_GET_ID_EXP(exp) \
  (BTOR_IS_INVERTED_EXP (exp) ? -BTOR_REAL_ADDR_EXP (exp)->id : exp->id)
#define BTOR_AIGVEC_EXP(btor, exp)                                     \
  (BTOR_IS_INVERTED_EXP (exp)                                          \
       ? btor_not_aigvec ((btor)->avmgr, BTOR_REAL_ADDR_EXP (exp)->av) \
       : btor_copy_aigvec ((btor)->avmgr, exp->av))
#define BTOR_BITS_EXP(mm, exp)                               \
  (BTOR_IS_INVERTED_EXP (exp)                                \
       ? btor_not_const (mm, BTOR_REAL_ADDR_EXP (exp)->bits) \
       : btor_copy_const (mm, exp->bits))

#define BTOR_TAG_EXP(exp, tag) \
  ((BtorExp *) ((unsigned long int) tag | (unsigned long int) (exp)))
#define BTOR_GET_TAG_EXP(exp) ((int) (3ul & (unsigned long int) (exp)))
#define BTOR_REAL_ADDR_EXP(exp) ((BtorExp *) (~3ul & (unsigned long int) (exp)))
#define BTOR_IS_REGULAR_EXP(exp) (!(3ul & (unsigned long int) (exp)))

#define BTOR_IS_ACC_EXP(exp) (BTOR_IS_READ_EXP (exp) || BTOR_IS_WRITE_EXP (exp))
#define BTOR_GET_INDEX_ACC_EXP(exp) ((exp)->e[1])
#define BTOR_GET_VALUE_ACC_EXP(exp) \
  (BTOR_IS_READ_EXP (exp) ? (exp) : (exp)->e[2])
#define BTOR_ACC_TARGET_EXP(exp) (BTOR_IS_READ_EXP (exp) ? (exp)->e[0] : (exp))
#define BTOR_IS_SYNTH_EXP(exp) ((exp)->av != NULL)

/*------------------------------------------------------------------------*/
/* Btor                                                                   */
/*------------------------------------------------------------------------*/

/* Creates new boolector instance. */
Btor *btor_new_btor (void);

/* Sets rewrite level [0,2]. */
void btor_set_rewrite_level_btor (Btor *btor, int rewrite_level);

/* Enables model generation. */
void btor_enable_model_gen (Btor *btor);

/* This enables further optimizations
 * as Boolector is used as a standalone SMT
 * solver which implies that btor_sat_btor
 * is called only once */
void btor_set_stand_alone_mode (Btor *btor);

/* Sets verbosity [-1,3] of btor and all sub-components
 * if verbosity is set to -1, then boolector is in "quiet mode" and
 * does not print any output.
 */
void btor_set_verbosity_btor (Btor *btor, int verbosity);

void btor_enable_under_approx (Btor *btor);

void btor_set_under_approx_initial_effective_width (Btor *btor,
                                                    int ua_start_width);

void btor_set_under_approx_mode (Btor *btor, BtorUAMode mode);

void btor_set_under_approx_ref (Btor *btor, BtorUARef ua_ref);

void btor_set_under_approx_enc (Btor *btor, BtorUAEnc ua_bw_enc);

/* Turns replay on or off. */
void btor_set_replay_btor (Btor *btor, int replay);

/* Deletes boolector. */
void btor_delete_btor (Btor *btor);

/* Gets version. */
const char *btor_version (Btor *btor);

/* Prints statistics. */
void btor_print_stats_btor (Btor *btor);

/*------------------------------------------------------------------------*/
/* BtorExp                                                                */
/*------------------------------------------------------------------------*/

/* Implicit precondition of all functions taking expressions as inputs:
 * The length 'len' of all input expressions have to be greater than zero.
 */

/* Binary constant.
 * strlen(bits) > 0
 * len(result) = strlen(bits)
 */
BtorExp *btor_const_exp (Btor *btor, const char *bits);

/* Binary constant representing 'len' zeros.
 * len > 0
 * len(result) = len
 */
BtorExp *btor_zero_exp (Btor *btor, int len);

/* Constant respresenting FALSE
 * len(result) = 1
 */
BtorExp *btor_false_exp (Btor *btor);

/* Binary constant representing 'len' ones.
 * len > 0
 * len(result) = len
 */
BtorExp *btor_ones_exp (Btor *btor, int len);

/* Constant respresenting TRUE
 * len(result) = 1
 */
BtorExp *btor_true_exp (Btor *btor);

/* Binary constant representing 1 with 'len' bits.
 * len > 0
 * len(result) = len
 */
BtorExp *btor_one_exp (Btor *btor, int len);

/* Binary constant representing the unsigned integer.
 * The constant is obtained by either truncating bits
 * or by unsigned extension (padding with zeroes).
 * len > 0
 */
BtorExp *btor_unsigned_to_exp (Btor *btor, unsigned u, int len);

/* Binary constant representing the signed integer.
 * The constant is obtained by either truncating bits
 * or by signed extension (padding with ones).
 * len > 0
 */
BtorExp *btor_int_to_exp (Btor *emg, int i, int len);

/* Variable representing 'len' bits.
 * len > 0
 * len(result) = len
 */
BtorExp *btor_var_exp (Btor *btor, int len, const char *symbol);

/* Array of size 2 ^ 'index_len' with elements of length 'elem_len'.
 * elem_len > 0
 * index_len > 0
 */
BtorExp *btor_array_exp (Btor *btor,
                         int elem_len,
                         int index_len,
                         const char *symbol);

/* One's complement.
 * len(result) = len(exp)
 */
BtorExp *btor_not_exp (Btor *btor, BtorExp *exp);

/* Two's complement.
 * len(result) = len(exp)
 */
BtorExp *btor_neg_exp (Btor *btor, BtorExp *exp);

/* OR reduction.
 * len(result) = 1
 */
BtorExp *btor_redor_exp (Btor *btor, BtorExp *exp);

/* XOR reduction.
 * len(result) = 1
 */
BtorExp *btor_redxor_exp (Btor *btor, BtorExp *exp);

/* AND reduction.
 * len(result) = 1
 */
BtorExp *btor_redand_exp (Btor *btor, BtorExp *exp);

/* Slice a sub-vector from 'upper' to 'lower'.
 * upper < len(exp)
 * lower >= 0
 * upper >= lower
 * len(result) = upper - lower + 1
 */
BtorExp *btor_slice_exp (Btor *btor, BtorExp *exp, int upper, int lower);

/* Unsigned extension of 'len' bits.
 * len >= 0
 * len(result) = len(exp) + len
 */
BtorExp *btor_uext_exp (Btor *btor, BtorExp *exp, int len);

/* Signed extension of 'len' bits (keep sign).
 * len >= 0
 * len(result) = len(exp) + len
 */
BtorExp *btor_sext_exp (Btor *btor, BtorExp *exp, int len);

/* Logical IMPLICATION.
 * len(e0) = len(e1) = 1
 * len(result) = 1
 */
BtorExp *btor_implies_exp (Btor *btor, BtorExp *e0, BtorExp *e1);

/* Logical EQUIVALENCE.
 * len(e0) = len(e1) = 1
 * len(result) = 1
 */
BtorExp *btor_iff_exp (Btor *btor, BtorExp *e0, BtorExp *e1);

/* Logical and bit-vector XOR.
 * len(e0) = len(e1)
 * len(result) = len(e0) = len(e1)
 */
BtorExp *btor_xor_exp (Btor *btor, BtorExp *e0, BtorExp *e1);

/* Logical and bit-vector XNOR.
 * len(e0) = len(e1)
 * len(result) = len(e0) = len(e1)
 */
BtorExp *btor_xnor_exp (Btor *btor, BtorExp *e0, BtorExp *e1);

/* Logical and bit-vector AND.
 * len(e0) = len(e1)
 * len(result) = len(e0) = len(e1)
 */
BtorExp *btor_and_exp (Btor *btor, BtorExp *e0, BtorExp *e1);

/* Logical and bit-vector NAND.
 * len(e0) = len(e1)
 * len(result) = len(e0) = len(e1)
 */
BtorExp *btor_nand_exp (Btor *btor, BtorExp *e0, BtorExp *e1);

/* Logical and bit-vector OR.
 * len(e0) = len(e1)
 * len(result) = len(e0) = len(e1)
 */
BtorExp *btor_or_exp (Btor *btor, BtorExp *e0, BtorExp *e1);

/* Logical and bit-vector NOR.
 * len(e0) = len(e1)
 * len(result) = len(e0) = len(e1)
 */
BtorExp *btor_nor_exp (Btor *btor, BtorExp *e0, BtorExp *e1);

/* Bit-vector or array equality.
 * len(e0) = len(e1)
 * len(result) = 1
 */
BtorExp *btor_eq_exp (Btor *btor, BtorExp *e0, BtorExp *e1);

/* Bit-vector or array inequality.
 * len(e0) = len(e1)
 * len(result) = 1
 */
BtorExp *btor_ne_exp (Btor *btor, BtorExp *e0, BtorExp *e1);

/* Adder.
 * len(e0) = len(e1)
 * len(result) = len(e0) = len(e1)
 */
BtorExp *btor_add_exp (Btor *btor, BtorExp *e0, BtorExp *e1);

/* Result represents if adding two unsigned operands leads to an overflow.
 * len(e0) = len(e1)
 * len(result) = 1
 */
BtorExp *btor_uaddo_exp (Btor *btor, BtorExp *e0, BtorExp *e1);

/* Result represents if adding two signed operands leads to an overflow.
 * len(e0) = len(e1)
 * len(result) = 1
 */
BtorExp *btor_saddo_exp (Btor *btor, BtorExp *e0, BtorExp *e1);

/* Multiplier.
 * len(e0) = len(e1)
 * len(result) = len(e0) = len(e1)
 */
BtorExp *btor_mul_exp (Btor *btor, BtorExp *e0, BtorExp *e1);

/* Result represents if multiplying two unsigned operands leads to an overflow.
 * len(e0) = len(e1)
 * len(result) = 1
 */
BtorExp *btor_umulo_exp (Btor *btor, BtorExp *e0, BtorExp *e1);

/* Result represents if multiplying two signed operands leads to an overflow.
 * len(e0) = len(e1)
 * len(result) = 1
 */
BtorExp *btor_smulo_exp (Btor *btor, BtorExp *e0, BtorExp *e1);

/* Unsigned less than.
 * len(e0) = len(e1)
 * len(result) = 1
 */
BtorExp *btor_ult_exp (Btor *btor, BtorExp *e0, BtorExp *e1);

/* Signed less than.
 * len(e0) = len(e1)
 * len(result) = 1
 */
BtorExp *btor_slt_exp (Btor *btor, BtorExp *e0, BtorExp *e1);

/* Unsigned less than or equal.
 * len(e0) = len(e1)
 * len(result) = 1
 */
BtorExp *btor_ulte_exp (Btor *btor, BtorExp *e0, BtorExp *e1);

/* Signed less than or equal.
 * len(e0) = len(e1)
 * len(result) = 1
 */
BtorExp *btor_slte_exp (Btor *btor, BtorExp *e0, BtorExp *e1);

/* Unsigned greater than.
 * len(e0) = len(e1)
 * len(result) = 1
 */
BtorExp *btor_ugt_exp (Btor *btor, BtorExp *e0, BtorExp *e1);

/* Signed greater than.
 * len(e0) = len(e1)
 * len(result) = 1
 */
BtorExp *btor_sgt_exp (Btor *btor, BtorExp *e0, BtorExp *e1);

/* Unsigned greater than or equal.
 * len(e0) = len(e1)
 * len(result) = 1
 */
BtorExp *btor_ugte_exp (Btor *btor, BtorExp *e0, BtorExp *e1);

/* Signed greater than or equal.
 * len(e0) = len(e1)
 * len(result) = 1
 */
BtorExp *btor_sgte_exp (Btor *btor, BtorExp *e0, BtorExp *e1);

/* Shift left logical.
 * is_power_of_2(len(e0))
 * len(e1) = log2(len(e0))
 * len(result) len(e0)
 */
BtorExp *btor_sll_exp (Btor *btor, BtorExp *e0, BtorExp *e1);

/* Shift right logical.
 * is_power_of_2(len(e0))
 * len(e1) = log2(len(e0))
 * len(result) = len(e0)
 */
BtorExp *btor_srl_exp (Btor *btor, BtorExp *e0, BtorExp *e1);

/* Shift right arithmetic.
 * is_power_of_2(len(e0))
 * len(e1) = log2(len(e0))
 * len(result) = len(e0)
 */
BtorExp *btor_sra_exp (Btor *btor, BtorExp *e0, BtorExp *e1);

/* Rotate left.
 * is_power_of_2(len(e0))
 * len(e1) = log2(len(e0))
 * len(result) = len(e0)
 */
BtorExp *btor_rol_exp (Btor *btor, BtorExp *e0, BtorExp *e1);

/* Rotate right.
 * is_power_of_2(len(e0))
 * len(e1) = log2(len(e0))
 * len(result) = len(e0)
 */
BtorExp *btor_ror_exp (Btor *btor, BtorExp *e0, BtorExp *e1);

/* Subtractor.
 * len(e0) = len(e1)
 * len(result) = len(e0) = len(e1)
 */
BtorExp *btor_sub_exp (Btor *btor, BtorExp *e0, BtorExp *e1);

/* Result represents if e0 - e1 leads to an overflow if both are unsigned.
 * len(e0) = len(e1)
 * len(result) = 1
 */
BtorExp *btor_usubo_exp (Btor *btor, BtorExp *e0, BtorExp *e1);

/* Result represents if e0 - e1 leads to an overflow if both are signed.
 * len(e0) = len(e1)
 * len(result) = 1
 */
BtorExp *btor_ssubo_exp (Btor *btor, BtorExp *e0, BtorExp *e1);

/* Unsigned divider.
 * len(e0) = len(e1)
 * len(result) = len(e0) = len(e1)
 */
BtorExp *btor_udiv_exp (Btor *btor, BtorExp *e0, BtorExp *e1);

/* Signed divider.
 * len(e0) = len(e1)
 * len(result) = len(e0) = len(e1)
 */
BtorExp *btor_sdiv_exp (Btor *btor, BtorExp *e0, BtorExp *e1);

/* Result represents if e0 / e1 leads to an overflow if both are signed.
 * For example INT_MIN / -1.
 * len(e0) = len(e1)
 * len(result) = 1
 */
BtorExp *btor_sdivo_exp (Btor *btor, BtorExp *e0, BtorExp *e1);

/* Unsigned modulo.
 * len(e0) = len(e1)
 * len(result) = len(e0) = len(e1)
 */
BtorExp *btor_urem_exp (Btor *btor, BtorExp *e0, BtorExp *e1);

/* Signed modulo.
 * len(e0) = len(e1)
 * len(result) = len(e0) = len(e1)
 */
BtorExp *btor_srem_exp (Btor *btor, BtorExp *e0, BtorExp *e1);

/* Signed modulo variant.
 * len(e0) = len(e1)
 * len(result) = len(e0) = len(e1)
 */
BtorExp *btor_smod_exp (Btor *btor, BtorExp *e0, BtorExp *e1);

/* Concatenation.
 * len(result) = len(e0) + len(e1)
 */
BtorExp *btor_concat_exp (Btor *btor, BtorExp *e0, BtorExp *e1);

/* Array read on array 'e_array' at position 'e_index'.
 * index_len(e_array) = len(e_index)
 * len(result) = elem_len(e_array)
 */
BtorExp *btor_read_exp (Btor *btor, BtorExp *e_array, BtorExp *e_index);

/* Array write on array 'e_array' at position 'e_index' with value 'e_value'.
 * index_len(e_array) = len(e_index)
 * elem_len(e_array) = len(e_value)
 */
BtorExp *btor_write_exp (Btor *btor,
                         BtorExp *e_array,
                         BtorExp *e_index,
                         BtorExp *e_value);

/* If-then-else.
 * len(e_cond) = 1
 * len(e_if) = len(e_else)
 * len(result) = len(e_if) = len(e_else)
 */
BtorExp *btor_cond_exp (Btor *btor,
                        BtorExp *e_cond,
                        BtorExp *e_if,
                        BtorExp *e_else);

/* Increments bit-vector expression by one */
BtorExp *btor_inc_exp (Btor *btor, BtorExp *exp);

/* Decrements bit-vector expression by one */
BtorExp *btor_dec_exp (Btor *btor, BtorExp *exp);

/* Gets the length of an expression representing the number of bits. */
int btor_get_exp_len (Btor *btor, BtorExp *exp);

/* Determines if expression is an array or not. */
int btor_is_array_exp (Btor *btor, BtorExp *exp);

/* Gets the number of bits used by indices on 'e_array'. */
int btor_get_index_exp_len (Btor *btor, BtorExp *e_array);

/* Gets the symbol of a variable. */
char *btor_get_symbol_exp (Btor *btor, BtorExp *exp);

/* Copies expression (increments reference counter). */
BtorExp *btor_copy_exp (Btor *btor, BtorExp *exp);

/* Releases expression (decrements reference counter). */
void btor_release_exp (Btor *btor, BtorExp *exp);

/* Dumps expression(s) to file in BTOR format. */
void btor_dump_exp (Btor *btor, FILE *file, BtorExp *root);
void btor_dump_exps (Btor *btor, FILE *file, BtorExp **exps, int nroots);
void btor_dump_exps_after_full_rewriting (Btor *btor,
                                          FILE *file,
                                          BtorExp **exps,
                                          int nroots);

/* Dumps expression to file in SMT format. */
void btor_dump_smt (Btor *btor, FILE *file, BtorExp *root);

/* Adds top level constraint. */
void btor_add_constraint_exp (Btor *btor, BtorExp *exp);

/* Dump added constraints and current assumptions to file 'file'. */
void btor_replay_btor (Btor *btor, FILE *file);

/* Adds assumption. */
void btor_add_assumption_exp (Btor *btor, BtorExp *exp);

/* Solves SAT instance.
 * The paramenter 'refinement_limit' sets the maximum number
 * of iterative refinments. If 'refinement_limit' is -1,
 * then no refinement limit is set.
 */
int btor_sat_btor (Btor *btor, int refinement_limit);

/* Builds current assignment string of expression (in the SAT case)
 * and returns it.
 * Do not call before calling btor_sat_exp.
 * strlen(result) = len(exp)
 */
char *btor_bv_assignment_exp (Btor *btor, BtorExp *exp);

void btor_array_assignment_exp (
    Btor *btor, BtorExp *exp, char ***indices, char ***values, int *size);

/* Frees BV assignment obtained by calling 'btor_assignment_exp' */
void btor_free_bv_assignment_exp (Btor *btor, char *assignment);

/*------------------------------------------------------------------------*/
/* Low-level BtorExp                                                      */
/*------------------------------------------------------------------------*/

BtorExp *btor_slice_exp_node (Btor *btor, BtorExp *exp, int upper, int lower);

BtorExp *btor_and_exp_node (Btor *btor, BtorExp *e0, BtorExp *e1);

BtorExp *btor_eq_exp_node (Btor *btor, BtorExp *e0, BtorExp *e1);

BtorExp *btor_add_exp_node (Btor *btor, BtorExp *e0, BtorExp *e1);

BtorExp *btor_mul_exp_node (Btor *btor, BtorExp *e0, BtorExp *e1);

BtorExp *btor_ult_exp_node (Btor *btor, BtorExp *e0, BtorExp *e1);

BtorExp *btor_sll_exp_node (Btor *btor, BtorExp *e0, BtorExp *e1);

BtorExp *btor_srl_exp_node (Btor *btor, BtorExp *e0, BtorExp *e1);

BtorExp *btor_udiv_exp_node (Btor *btor, BtorExp *e0, BtorExp *e1);

BtorExp *btor_urem_exp_node (Btor *btor, BtorExp *e0, BtorExp *e1);

BtorExp *btor_concat_exp_node (Btor *btor, BtorExp *e0, BtorExp *e1);

BtorExp *btor_read_exp_node (Btor *btor, BtorExp *e_array, BtorExp *e_index);

BtorExp *btor_write_exp_node (Btor *btor,
                              BtorExp *e_array,
                              BtorExp *e_index,
                              BtorExp *e_value);

BtorExp *btor_cond_exp_node (Btor *btor,
                             BtorExp *e_cond,
                             BtorExp *e_if,
                             BtorExp *e_else);

/*------------------------------------------------------------------------*/
/* Misc                                                                   */
/*------------------------------------------------------------------------*/

/* Synthesizes expression of arbitrary length to an AIG vector. Adds string
 * back annotation to the hash table, if the hash table is a non zero ptr.
 * The strings in 'data.asStr' are owned by the caller.  The hash table
 * is a map from AIG variables to strings.
 */
BtorAIGVec *btor_exp_to_aigvec (Btor *btor,
                                BtorExp *exp,
                                BtorPtrHashTable *table);

/* Marks all reachable expressions with new mark. */
void btor_mark_exp (Btor *btor, BtorExp *exp, int new_mark);

/* Symbolically applies next function for model checking */
BtorExp *btor_next_exp_bmc (Btor *btor,
                            BtorPtrHashTable *reg_table,
                            BtorExp *root,
                            int k,
                            BtorPtrHashTable *input_table);

/* Hashes expression by ID */
unsigned int btor_hash_exp_by_id (BtorExp *exp);

/* Compares two expression pairs by ID */
int btor_compare_exp_by_id (BtorExp *exp0, BtorExp *exp1);

/* Finds most simplified expression and shortens path to it */
BtorExp *btor_pointer_chase_simplified_exp (Btor *btor, BtorExp *exp);

/*------------------------------------------------------------------------*/
/* Debugging                                                              */
/*------------------------------------------------------------------------*/

#ifndef NDEBUG

int btor_precond_slice_exp_dbg (const Btor *btor,
                                const BtorExp *exp,
                                int upper,
                                int lower);

int btor_precond_ext_exp_dbg (const Btor *btor, const BtorExp *exp, int len);

int btor_precond_regular_unary_bv_exp_dbg (const Btor *btor,
                                           const BtorExp *exp);

int btor_precond_eq_exp_dbg (const Btor *btor,
                             const BtorExp *e0,
                             const BtorExp *e1);

int btor_precond_shift_exp_dbg (const Btor *btor,
                                const BtorExp *e0,
                                const BtorExp *e1);

int btor_precond_concat_exp_dbg (const Btor *btor,
                                 const BtorExp *e0,
                                 const BtorExp *e1);

int btor_precond_regular_binary_bv_exp_dbg (const Btor *btor,
                                            const BtorExp *e0,
                                            const BtorExp *e1);

int btor_precond_read_exp_dbg (const Btor *btor,
                               const BtorExp *e_array,
                               const BtorExp *e_index);

int btor_precond_write_exp_dbg (const Btor *btor,
                                const BtorExp *e_array,
                                const BtorExp *e_index,
                                const BtorExp *e_value);

int btor_precond_cond_exp_dbg (const Btor *btor,
                               const BtorExp *e_cond,
                               const BtorExp *e_if,
                               const BtorExp *e_else);

#endif

#endif
