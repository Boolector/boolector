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
  BTOR_CONST_EXP,
  BTOR_VAR_EXP,
  BTOR_ARRAY_EXP,
  BTOR_SLICE_EXP,
  BTOR_AND_EXP,
  BTOR_EQ_EXP,
  BTOR_ADD_EXP,
  BTOR_MUL_EXP,
  BTOR_ULT_EXP,
  BTOR_SLL_EXP,
  BTOR_SRL_EXP,
  BTOR_UDIV_EXP,
  BTOR_UREM_EXP,
  BTOR_CONCAT_EXP,
  BTOR_READ_EXP,
  BTOR_WRITE_EXP,
  BTOR_COND_EXP
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

struct BtorReadObj
{
  BtorExp *var;
  BtorExp *index;
  int index_cnf_generated;
};

typedef struct BtorReadObj BtorReadObj;

BTOR_DECLARE_STACK (ReadObjPtr, BtorReadObj *);

struct BtorExp
{
  BtorExpKind kind : 5;  /* kind of expression */
  unsigned int mark : 3; /* for DAG traversal algorithms */
  int index_len;         /* for arrays and writes only */
  union
  {
    struct
    {
      char *symbol; /* for variables only */
      union
      {
        int upper;        /* for slices only */
        char *assignment; /* for variables only */
      };
      union
      {
        int lower;             /* for slices only */
        char *bits;            /* for constants only */
        BtorReadObj *read_obj; /* for reads only */
      };
    };
    struct BtorExp *e[3]; /* children */
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

#define BTOR_INVERT_EXP(exp) ((BtorExp *) (1ul ^ (unsigned long int) (exp)))
#define BTOR_IS_INVERTED_EXP(exp) (1ul & (unsigned long int) (exp))
#define BTOR_COND_INVERT_EXP(cond_exp, exp) \
  ((BTOR_IS_INVERTED_EXP (cond_exp) ? BTOR_INVERT_EXP (exp) : exp))
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

BTOR_DECLARE_STACK (ExpPtr, BtorExp *);

/* Sets the read encoding paradigm. */
void btor_set_read_enc_exp_mgr (BtorExpMgr *emgr, BtorReadEnc read_enc);

/* Sets the read encoding strategy. */
void btor_set_write_enc_exp_mgr (BtorExpMgr *emgr, BtorWriteEnc write_enc);

/* Returns the memory manager of the expression manager. */
BtorMemMgr *btor_get_mem_mgr_exp_mgr (BtorExpMgr *emgr);

/* Returns the AIG vector manager of the expression manager. */
BtorAIGVecMgr *btor_get_aigvec_mgr_exp_mgr (BtorExpMgr *emgr);

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

/* Converts boolean expression into SAT instance.
 * len(exp) = 1
 */
void btor_exp_to_sat (BtorExpMgr *emgr, BtorExp *exp);

/* Marks all reachable expressions with new mark. */
void btor_mark_exp (BtorExpMgr *emgr, BtorExp *exp, int new_mark);

#endif
