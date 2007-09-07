#ifndef BTOREXP_H_INCLUDED
#define BTOREXP_H_INCLUDED

#include "boolector.h"
#include "btoraigvec.h"
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
  BTOR_COND_EXP,
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

struct BtorReadObj
{
  BtorExp *var;
  BtorExp *index;
};

typedef struct BtorReadObj BtorReadObj;

BTOR_DECLARE_STACK (ReadObjPtr, BtorReadObj *);

struct BtorExp
{
  BtorExpKind kind;
  union
  {
    struct
    {
      union
      {
        char *symbol;                         /* for variables only */
        BtorReadObjPtrStack *read_constraint; /* for arrays only */
      };
      union
      {
        int upper;        /* for slices only */
        char *assignment; /* for variables only */
      };
      union
      {
        int lower;     /* for slices only */
        char *bits;    /* for constants only */
        int index_len; /* for arrays only */
      };
    };
    struct BtorExp *e[3]; /* children */
  };
  int len; /* number of bits */
  int id;
  int refs;
  int mark;
  BtorAIGVec *av;
  struct BtorExp *next;         /* next element in unique table */
  struct BtorExp *first_parent; /* head of parent list */
  struct BtorExp *last_parent;  /* tail of parent list */
  struct BtorExp *prev_parent[3];
  struct BtorExp *next_parent[3];
};

#define BTOR_IS_CONST_EXP_KIND(kind) ((kind) == BTOR_CONST_EXP)
#define BTOR_IS_VAR_EXP_KIND(kind) ((kind) == BTOR_VAR_EXP)
#define BTOR_IS_ARRAY_EXP_KIND(kind) ((kind) == BTOR_ARRAY_EXP)
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

void btor_set_read_enc_exp_mgr (BtorExpMgr *emgr, BtorReadEnc read_enc);

BtorMemMgr *btor_get_mem_mgr_exp_mgr (BtorExpMgr *emgr);

BtorAIGVecMgr *btor_get_aigvec_mgr_exp_mgr (BtorExpMgr *emgr);

BtorAIG *btor_exp_to_aig (BtorExpMgr *, BtorExp *); /* len=1 */

BtorAIGVec *btor_exp_to_aigs (BtorExpMgr *, BtorExp *); /* arb. len */

void btor_exp_to_sat (BtorExpMgr *emgr, BtorExp *exp);

void btor_mark_exp (BtorExpMgr *emgr, BtorExp *exp, int new_mark);

#endif
