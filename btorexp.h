#ifndef BTOREXP_H_INCLUDED
#define BTOREXP_H_INCLUDED

#include "boolector.h"
#include "btoraigvec.h"
#include "btorhash.h"
#include "btormem.h"
#include "btorqueue.h"
#include "btorstack.h"

/*------------------------------------------------------------------------*/
/* PRIVATE INTERFACE                                                      */
/*------------------------------------------------------------------------*/

enum BtorExpKind
{
  BTOR_CONST_EXP  = 0,
  BTOR_VAR_EXP    = 1,
  BTOR_ARRAY_EXP  = 2,
  BTOR_SLICE_EXP  = 3,
  BTOR_AND_EXP    = 4,
  BTOR_BEQ_EXP    = 5, /* equality on bit vectors */
  BTOR_AEQ_EXP    = 6, /* equality on arrays */
  BTOR_ADD_EXP    = 7,
  BTOR_MUL_EXP    = 8,
  BTOR_ULT_EXP    = 9,
  BTOR_SLL_EXP    = 10,
  BTOR_SRL_EXP    = 11,
  BTOR_UDIV_EXP   = 12,
  BTOR_UREM_EXP   = 13,
  BTOR_CONCAT_EXP = 14,
  BTOR_READ_EXP   = 15,
  BTOR_WRITE_EXP  = 16,
  BTOR_BCOND_EXP  = 17, /* conditional on bit vectors */
  BTOR_ACOND_EXP  = 18, /* conditional on arrays */
};

typedef enum BtorExpKind BtorExpKind;

enum BtorReadEnc
{
  BTOR_EAGER_READ_ENC,
  BTOR_LAZY_READ_ENC,
};

typedef enum BtorReadEnc BtorReadEnc;

enum BtorWriteEnc
{
  BTOR_EAGER_WRITE_ENC,
  BTOR_LAZY_WRITE_ENC
};

typedef enum BtorWriteEnc BtorWriteEnc;

typedef struct BtorExpPair BtorExpPair;

#define BTOR_BASIC_EXP                                                       \
  struct                                                                     \
  {                                                                          \
    BtorExpKind kind : 5;          /* kind of expression */                  \
    unsigned int mark : 3;         /* for DAG traversal */                   \
    unsigned int array_mark : 3;   /* for bottom up array traversal */       \
    unsigned int encoded_read : 1; /* flag used by eager read encoding */    \
    unsigned int reachable : 1;    /* flag determines if expression          \
                                      is reachable from root */              \
    unsigned int full_sat : 1;     /* flag determines if expression has been \
                                      fully encoded into SAT */              \
    unsigned int vread : 1;        /* flag determines if expression          \
                                      is a virtual read */                   \
    union                                                                    \
    {                                                                        \
      struct                                                                 \
      {                                                                      \
        char *symbol; /* symbol of variables for output */                   \
        int upper;    /* upper index for slices */                           \
        union                                                                \
        {                                                                    \
          int lower;           /* lower index for slices */                  \
          char *bits;          /* bit vector of constants */                 \
          BtorExpPair *vreads; /* virtual reads for array equalites */       \
        };                                                                   \
      };                                                                     \
      struct BtorExp *e[3]; /* three expression children */                  \
    };                                                                       \
    int len;                        /* number of bits */                     \
    int id;                         /* unique expression id */               \
    int refs;                       /* reference counter */                  \
    BtorAIGVec *av;                 /* synthesized AIG vector */             \
    struct BtorExp *next;           /* next element in unique table */       \
    struct BtorExp *first_parent;   /* head of parent list */                \
    struct BtorExp *last_parent;    /* tail of parent list */                \
    struct BtorExp *prev_parent[3]; /* prev exp in parent list of child i */ \
    struct BtorExp *next_parent[3]; /* next exp in parent list of child i */ \
    struct BtorExp *parent;         /* parent pointer for BFS */             \
    struct BtorExp *simplified;     /* equivalent simplified expression */   \
    Btor *btor;                     /* boolector */                          \
  }

#define BTOR_ADDITIONAL_ARRAY_EXP                                             \
  struct                                                                      \
  {                                                                           \
    int index_len;                          /* length of the index */         \
    BtorPtrHashTable *table;                /* used for determining read-read \
                                               and read-write conflicts */    \
    struct BtorExp *first_aeq_acond_parent; /* first array equality or array  \
                                               conditional in parent list */  \
    struct BtorExp *last_aeq_acond_parent;  /* last array equality or array   \
                                               conditional in parent list */  \
    struct BtorExp *prev_aeq_acond_parent[3]; /* prev array equality or       \
                                                 conditional in aeq acond     \
                                                 parent list of child i */    \
    struct BtorExp *next_aeq_acond_parent[3]; /* next array equality or       \
                                                 conditional in aeq acond     \
                                                 parent list of child i */    \
  }

struct BtorBasicExp
{
  BTOR_BASIC_EXP;
};

typedef struct BtorBasicExp BtorBasicExp;

struct BtorExp
{
  BTOR_BASIC_EXP;
  BTOR_ADDITIONAL_ARRAY_EXP;
};

#define BTOR_IS_CONST_EXP_KIND(kind) ((kind) == BTOR_CONST_EXP)
#define BTOR_IS_VAR_EXP_KIND(kind) ((kind) == BTOR_VAR_EXP)
#define BTOR_IS_ARRAY_EXP_KIND(kind)                        \
  (((kind) == BTOR_ARRAY_EXP) || ((kind) == BTOR_WRITE_EXP) \
   || ((kind) == BTOR_ACOND_EXP))
#define BTOR_IS_NATIVE_ARRAY_EXP_KIND(kind) (kind == BTOR_ARRAY_EXP)
#define BTOR_IS_WRITE_ARRAY_EXP_KIND(kind) (kind == BTOR_WRITE_EXP)
#define BTOR_IS_COND_ARRAY_EXP_KIND(kind) (kind == BTOR_ACOND_EXP)
#define BTOR_IS_UNARY_EXP_KIND(kind) ((kind) == BTOR_SLICE_EXP)
#define BTOR_IS_BINARY_EXP_KIND(kind) \
  (((kind) >= BTOR_AND_EXP) && ((kind) <= BTOR_READ_EXP))
#define BTOR_IS_BINARY_COMMUTATIVE_EXP_KIND(kind) \
  (((kind) >= BTOR_AND_EXP) && ((kind) <= BTOR_MUL_EXP))
#define BTOR_IS_TERNARY_EXP_KIND(kind)                  \
  ((kind) == BTOR_WRITE_EXP || (kind) == BTOR_BCOND_EXP \
   || (kind) == BTOR_ACOND_EXP)

#define BTOR_IS_CONST_EXP(exp) (BTOR_IS_CONST_EXP_KIND ((exp)->kind))
#define BTOR_IS_VAR_EXP(exp) (BTOR_IS_VAR_EXP_KIND ((exp)->kind))
#define BTOR_IS_ARRAY_EXP(exp) (BTOR_IS_ARRAY_EXP_KIND ((exp)->kind))
#define BTOR_IS_NATIVE_ARRAY_EXP(exp) \
  (BTOR_IS_NATIVE_ARRAY_EXP_KIND ((exp)->kind))
#define BTOR_IS_WRITE_ARRAY_EXP(exp) \
  (BTOR_IS_WRITE_ARRAY_EXP_KIND ((exp)->kind))
#define BTOR_IS_COND_ARRAY_EXP(exp) (BTOR_IS_COND_ARRAY_EXP_KIND ((exp)->kind))
#define BTOR_IS_UNARY_EXP(exp) (BTOR_IS_UNARY_EXP_KIND ((exp)->kind))
#define BTOR_IS_BINARY_EXP(exp) (BTOR_IS_BINARY_EXP_KIND ((exp)->kind))
#define BTOR_IS_TERNARY_EXP(exp) (BTOR_IS_TERNARY_EXP_KIND ((exp)->kind))

#define BTOR_ARITY_EXP(exp) \
  (BTOR_IS_UNARY_EXP (exp)  \
       ? 1                  \
       : BTOR_IS_BINARY_EXP (exp) ? 2 : BTOR_IS_TERNARY_EXP (exp) ? 3 : 0)

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

#define BTOR_IS_ACC_EXP(exp) \
  ((exp)->kind == BTOR_READ_EXP || BTOR_IS_WRITE_ARRAY_EXP (exp))
#define BTOR_GET_INDEX_ACC_EXP(exp) ((exp)->e[1])
#define BTOR_GET_VALUE_ACC_EXP(exp) \
  ((exp)->kind == BTOR_READ_EXP ? (exp) : (exp)->e[2])
#define BTOR_ACC_TARGET_EXP(exp) \
  ((exp)->kind == BTOR_READ_EXP ? (exp)->e[0] : (exp))

BTOR_DECLARE_STACK (ExpPtr, BtorExp *);

BTOR_DECLARE_QUEUE (ExpPtr, BtorExp *);

/* Sets the read encoding paradigm. */
void btor_set_read_enc_btor (Btor *btor, BtorReadEnc read_enc);

/* Sets the read encoding strategy. */
void btor_set_write_enc_btor (Btor *btor, BtorWriteEnc write_enc);

/* Prints statistics */
void btor_print_stats_btor (Btor *btor);

/* Returns the memory manager. */
BtorMemMgr *btor_get_mem_mgr_btor (const Btor *btor);

/* Returns the AIG vector manager. */
BtorAIGVecMgr *btor_get_aigvec_mgr_btor (const Btor *btor);

/* Synthesizes formula represented by top
 * level constraints and assumptions to a single AIG.
 */
BtorAIG *btor_to_aig_exp (Btor *btor);

/* Synthesizes expression of arbitrary length to an AIG vector. Adds string
 * back annotation to the hash table, if the hash table is a non zero ptr.
 * The strings in 'data.asStr' are owned by the caller.  The hash table
 * is a map from AIG variables to strings.
 */
BtorAIGVec *btor_exp_to_aigvec (Btor *btor,
                                BtorExp *exp,
                                BtorPtrHashTable *table);

/* Translates formula represented by top level constraints
 * and assumptions into SAT instance.
 */
void btor_to_sat_exp (Btor *btor);

/* Marks all reachable expressions with new mark. */
void btor_mark_exp (Btor *btor, BtorExp *exp, int new_mark);

#endif
