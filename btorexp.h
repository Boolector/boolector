#ifndef BTOREXP_H_INCLUDED
#define BTOREXP_H_INCLUDED

#include "boolector.h"
#include "btoraigvec.h"
#include "btorhash.h"
#include "btormem.h"
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
  BTOR_EQ_EXP     = 5,
  BTOR_ADD_EXP    = 6,
  BTOR_MUL_EXP    = 7,
  BTOR_ULT_EXP    = 8,
  BTOR_SLL_EXP    = 9,
  BTOR_SRL_EXP    = 10,
  BTOR_UDIV_EXP   = 11,
  BTOR_UREM_EXP   = 12,
  BTOR_CONCAT_EXP = 13,
  BTOR_READ_EXP   = 14,
  BTOR_WRITE_EXP  = 15,
  BTOR_COND_EXP   = 16,
};

typedef enum BtorExpKind BtorExpKind;

enum BtorReadEnc
{
  BTOR_NO_READ_ENC,
  BTOR_EAGER_READ_ENC,
  BTOR_LAZY_READ_ENC,
  BTOR_SAT_SOLVER_READ_ENC
};

typedef enum BtorReadEnc BtorReadEnc;

enum BtorWriteEnc
{
  BTOR_NO_WRITE_ENC,
  BTOR_EAGER_WRITE_ENC,
  BTOR_LAZY_WRITE_ENC
};

typedef enum BtorWriteEnc BtorWriteEnc;

struct BtorExp
{
  BtorExpKind kind : 5;          /* kind of expression */
  unsigned int mark : 3;         /* for DAG traversal algorithms */
  unsigned int encoded_read : 1; /* flag used by eager read encoding */
  unsigned int reachable : 1;    /* flag determines if expression
                                    is reachable from root or not */
  unsigned int full_cnf : 1;     /* determines if exp has been
                                    fully encoded into CNF */
  int index_len;                 /* for arrays and writes only */
  struct BtorExpPtrStack *reads; /* used for sorting read parents. */
                                 /* for arrays and writes only */
  union
  {
    struct
    {
      char *symbol; /* symbol for output. for variables only */
      int upper;    /* for slices only */
      union
      {
        int lower;  /* for slices only */
        char *bits; /* for constants only */
      };
    };
    struct BtorExp *e[3]; /* three children */
  };
  int len;                        /* number of bits */
  int id;                         /* unique expression id */
  int refs;                       /* reference counter */
  BtorAIGVec *av;                 /* synthesized AIG vector */
  struct BtorExp *next;           /* next element in unique table */
  struct BtorExp *first_parent;   /* head of parent list */
  struct BtorExp *last_parent;    /* tail of parent list */
  struct BtorExp *prev_parent[3]; /* prev exp in parent list of child i */
  struct BtorExp *next_parent[3]; /* next exp in parent list of child i */
  BtorExpMgr *emgr;               /* expression manager */
};

#define BTOR_IS_CONST_EXP_KIND(kind) ((kind) == BTOR_CONST_EXP)
#define BTOR_IS_VAR_EXP_KIND(kind) ((kind) == BTOR_VAR_EXP)
#define BTOR_IS_ARRAY_EXP_KIND(kind) \
  (((kind) == BTOR_ARRAY_EXP) || ((kind) == BTOR_WRITE_EXP))
#define BTOR_IS_NATIVE_ARRAY_EXP_KIND(kind) (kind == BTOR_ARRAY_EXP)
#define BTOR_IS_WRITE_ARRAY_EXP_KIND(kind) (kind == BTOR_WRITE_EXP)
#define BTOR_IS_UNARY_EXP_KIND(kind) ((kind) == BTOR_SLICE_EXP)
#define BTOR_IS_BINARY_EXP_KIND(kind) \
  (((kind) >= BTOR_AND_EXP) && ((kind) <= BTOR_READ_EXP))
#define BTOR_IS_BINARY_COMMUTATIVE_EXP_KIND(kind) \
  (((kind) >= BTOR_AND_EXP) && ((kind) <= BTOR_MUL_EXP))
#define BTOR_IS_TERNARY_EXP_KIND(kind) \
  ((kind) == BTOR_WRITE_EXP || (kind) == BTOR_COND_EXP)

#define BTOR_IS_CONST_EXP(exp) (BTOR_IS_CONST_EXP_KIND ((exp)->kind))
#define BTOR_IS_VAR_EXP(exp) (BTOR_IS_VAR_EXP_KIND ((exp)->kind))
#define BTOR_IS_ARRAY_EXP(exp) (BTOR_IS_ARRAY_EXP_KIND ((exp)->kind))
#define BTOR_IS_NATIVE_ARRAY_EXP(exp) \
  (BTOR_IS_NATIVE_ARRAY_EXP_KIND ((exp)->kind))
#define BTOR_IS_WRITE_ARRAY_EXP(exp) \
  (BTOR_IS_WRITE_ARRAY_EXP_KIND ((exp)->kind))
#define BTOR_IS_UNARY_EXP(exp) (BTOR_IS_UNARY_EXP_KIND ((exp)->kind))
#define BTOR_IS_BINARY_EXP(exp) (BTOR_IS_BINARY_EXP_KIND ((exp)->kind))
#define BTOR_IS_TERNARY_EXP(exp) (BTOR_IS_TERNARY_EXP_KIND ((exp)->kind))

#define BTOR_ARITY_EXP(exp) \
  (BTOR_IS_UNARY_EXP (exp)  \
       ? 1                  \
       : BTOR_IS_BINARY_EXP (exp) ? 2 : BTOR_IS_TERNARY_EXP (exp) ? 3 : 0)

#define BTOR_INVERT_EXP(exp) ((BtorExp *) (1ul ^ (unsigned long int) (exp)))
#define BTOR_IS_INVERTED_EXP(exp) (1ul & (unsigned long int) (exp))
#define BTOR_COND_INVERT_EXP(cond_exp, exp) \
  ((BTOR_IS_INVERTED_EXP (cond_exp) ? BTOR_INVERT_EXP (exp) : exp))
#define BTOR_GET_ID_EXP(exp) \
  (BTOR_IS_INVERTED_EXP (exp) ? -BTOR_REAL_ADDR_EXP (exp)->id : exp->id)
#define BTOR_GET_AIGVEC_EXP(emgr, exp)                                 \
  (BTOR_IS_INVERTED_EXP (exp)                                          \
       ? btor_not_aigvec ((emgr)->avmgr, BTOR_REAL_ADDR_EXP (exp)->av) \
       : btor_copy_aigvec ((emgr)->avmgr, exp->av))
#define BTOR_GET_BITS_EXP(mm, exp)                           \
  (BTOR_IS_INVERTED_EXP (exp)                                \
       ? btor_not_const (mm, BTOR_REAL_ADDR_EXP (exp)->bits) \
       : btor_copy_const (mm, exp->bits))

#define BTOR_TAG_EXP(exp, tag) \
  ((BtorExp *) ((unsigned long int) tag | (unsigned long int) (exp)))
#define BTOR_GET_TAG_EXP(exp) ((int) (3ul & (unsigned long int) (exp)))
#define BTOR_REAL_ADDR_EXP(exp) ((BtorExp *) (~3ul & (unsigned long int) (exp)))
#define BTOR_IS_REGULAR_EXP(exp) (!(3ul & (unsigned long int) (exp)))

BTOR_DECLARE_STACK (ExpPtr, BtorExp *);

/* Sets the read encoding paradigm. */
void btor_set_read_enc_exp_mgr (BtorExpMgr *emgr, BtorReadEnc read_enc);

/* Sets the read encoding strategy. */
void btor_set_write_enc_exp_mgr (BtorExpMgr *emgr, BtorWriteEnc write_enc);

/* Returns the memory manager of the expression manager. */
BtorMemMgr *btor_get_mem_mgr_exp_mgr (BtorExpMgr *emgr);

/* Returns the AIG vector manager of the expression manager. */
BtorAIGVecMgr *btor_get_aigvec_mgr_exp_mgr (BtorExpMgr *emgr);

/* Returns stack of all variables.
 * WARNING: DO NOT MODIFY THE STACK AND ITS CONTENTS */
const BtorExpPtrStack *btor_get_variables_exp_mgr (BtorExpMgr *emgr);

/* Returns stack of all arrays.
 * WARNING: DO NOT MODIFY THE STACK AND ITS CONTENTS */
const BtorExpPtrStack *btor_get_arrays_exp_mgr (BtorExpMgr *emgr);

/* Synthesize boolean expression to a single AIG.
 * len(exp) = 1
 */
BtorAIG *btor_exp_to_aig (BtorExpMgr *emgr, BtorExp *exp);

/* Synthesize expression of arbitrary length to an AIG vector.  Add string
 * back annotation to the hash table, if the hash table is a non zero ptr.
 * The strings in 'data.asStr' are owned by the caller.  The hash table
 * is a map from AIG variables to strings.
 */
BtorAIGVec *btor_exp_to_aigvec (BtorExpMgr *emgr,
                                BtorExp *exp,
                                BtorPtrHashTable *table);

/* Translates boolean expression into SAT instance.
 * len(exp) = 1
 */
void btor_exp_to_sat (BtorExpMgr *emgr, BtorExp *exp);

/* Marks all reachable expressions with new mark. */
void btor_mark_exp (BtorExpMgr *emgr, BtorExp *exp, int new_mark);

#endif
