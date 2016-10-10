/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015-2016 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORPROPSLS_H_INCLUDED
#define BTORPROPSLS_H_INCLUDED

#include "btorslvprop.h"
#include "btorslvsls.h"

#include "btorbitvec.h"
#include "btorexp.h"
#include "btorlog.h"
#include "btormodel.h"
#include "btortypes.h"
#include "utils/btorhashint.h"

/*------------------------------------------------------------------------*/

static inline void
btor_propsls_rec_conf (Btor* btor)
{
  assert (btor);
  assert (btor_get_opt (btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_PROP
          || btor_get_opt (btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_SLS);

  if (btor_get_opt (btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_PROP)
    BTOR_PROP_SOLVER (btor)->stats.move_prop_rec_conf += 1;
  else
    BTOR_SLS_SOLVER (btor)->stats.move_prop_rec_conf += 1;
}

static inline BtorBitVector*
btor_propsls_non_rec_conf (
    Btor* btor, BtorBitVector* bve, BtorBitVector* bvexp, int eidx, char* op)
{
  assert (btor);
  assert (btor_get_opt (btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_PROP
          || btor_get_opt (btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_SLS);
  assert (bve);
  assert (bvexp);
  assert (op);

  (void) bve;
  (void) bvexp;
  (void) eidx;
  (void) op;

#ifndef NDEBUG
  char* sbve   = btor_bv_to_char_bv (btor->mm, bve);
  char* sbvexp = btor_bv_to_char_bv (btor->mm, bvexp);
  if (eidx)
    BTORLOG (2, "prop CONFLICT: %s := %s %s x", sbvexp, sbve, op);
  else
    BTORLOG (2, "prop CONFLICT: %s := x %s %s", sbvexp, op, sbve);
  btor_freestr (btor->mm, sbve);
  btor_freestr (btor->mm, sbvexp);
#endif
  if (btor_get_opt (btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_PROP)
    BTOR_PROP_SOLVER (btor)->stats.move_prop_non_rec_conf += 1;
  else
    BTOR_SLS_SOLVER (btor)->stats.move_prop_non_rec_conf += 1;
  return 0;
}

/*------------------------------------------------------------------------*/

void btor_propsls_update_cone (Btor* btor,
                               BtorPtrHashTable* bv_model,
                               BtorIntHashTable* roots,
                               BtorPtrHashTable* score,
                               BtorIntHashTable* exps,
                               BtorBitVector* assignment,
                               uint64_t* stats_updates,
                               double* time_update_cone,
                               double* time_update_cone_reset,
                               double* time_update_cone_model_gen,
                               double* time_update_cone_compute_score);

void btor_propsls_compute_sls_scores (Btor* btor,
                                      BtorPtrHashTable* bv_model,
                                      BtorPtrHashTable* fun_model,
                                      BtorPtrHashTable* score);

#endif
