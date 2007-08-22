#ifndef BTORAIGVEC_H_INCLUDED
#define BTORAIGVEC_H_INCLUDED

#include "btoraig.h"
#include "btormem.h"

/*------------------------------------------------------------------------*/
/* PRIVATE INTERFACE                                                      */
/*------------------------------------------------------------------------*/

struct BtorAIGVec
{
  BtorAIG **aigs;
  int len;
};

typedef struct BtorAIGVec BtorAIGVec;

typedef struct BtorAIGVecMgr BtorAIGVecMgr;

BtorAIGVecMgr *btor_new_aigvec_mgr (BtorMemMgr *mm, int verbosity);

void btor_delete_aigvec_mgr (BtorAIGVecMgr *avmgr);

BtorAIGMgr *btor_get_aig_mgr_aigvec_mgr (BtorAIGVecMgr *avmgr);

BtorAIGVec *btor_const_aigvec (BtorAIGVecMgr *avmgr, const char *bits);

BtorAIGVec *btor_var_aigvec (BtorAIGVecMgr *avmgr, int len);

BtorAIGVec *btor_array_aigvec (BtorAIGVecMgr *avmgr,
                               int elem_len,
                               int index_len);

BtorAIGVec *btor_not_aigvec (BtorAIGVecMgr *avmgr, BtorAIGVec *av);

BtorAIGVec *btor_slice_aigvec (BtorAIGVecMgr *avmgr,
                               BtorAIGVec *av,
                               int upper,
                               int lower);

BtorAIGVec *btor_and_aigvec (BtorAIGVecMgr *avmgr,
                             BtorAIGVec *av1,
                             BtorAIGVec *av2);

BtorAIGVec *btor_ult_aigvec (BtorAIGVecMgr *avmgr,
                             BtorAIGVec *av1,
                             BtorAIGVec *av2);

BtorAIGVec *btor_eq_aigvec (BtorAIGVecMgr *avmgr,
                            BtorAIGVec *av1,
                            BtorAIGVec *av2);

BtorAIGVec *btor_add_aigvec (BtorAIGVecMgr *avmgr,
                             BtorAIGVec *av1,
                             BtorAIGVec *av2);

BtorAIGVec *btor_sll_aigvec (BtorAIGVecMgr *avmgr,
                             BtorAIGVec *av1,
                             BtorAIGVec *av2);

BtorAIGVec *btor_srl_aigvec (BtorAIGVecMgr *avmgr,
                             BtorAIGVec *av1,
                             BtorAIGVec *av2);

BtorAIGVec *btor_umul_aigvec (BtorAIGVecMgr *avmgr,
                              BtorAIGVec *av1,
                              BtorAIGVec *av2);

BtorAIGVec *btor_udiv_aigvec (BtorAIGVecMgr *avmgr,
                              BtorAIGVec *av1,
                              BtorAIGVec *av2);

BtorAIGVec *btor_umod_aigvec (BtorAIGVecMgr *avmgr,
                              BtorAIGVec *av1,
                              BtorAIGVec *av2);

BtorAIGVec *btor_concat_aigvec (BtorAIGVecMgr *avmgr,
                                BtorAIGVec *av1,
                                BtorAIGVec *av2);

BtorAIGVec *btor_acc_aigvec (BtorAIGVecMgr *avmgr,
                             BtorAIGVec *av_array,
                             BtorAIGVec *av_index);

BtorAIGVec *btor_cond_aigvec (BtorAIGVecMgr *avmgr,
                              BtorAIGVec *av_cond,
                              BtorAIGVec *av_if,
                              BtorAIGVec *av_else);

BtorAIGVec *btor_copy_aigvec (BtorAIGVecMgr *avmgr, BtorAIGVec *av);

void btor_release_delete_aigvec (BtorAIGVecMgr *avmgr, BtorAIGVec *av);

BtorAIGMgr *btor_get_aig_mgr_aigvec_mgr (BtorAIGVecMgr *avmgr);

char *btor_get_assignment_aigvec (BtorAIGVecMgr *avmgr, BtorAIGVec *av);

#endif
