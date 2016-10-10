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

#include "btorbitvec.h"
#include "btorexp.h"
#include "btormodel.h"
#include "btortypes.h"
#include "utils/btorhashint.h"

static inline void
btor_propsls_update_roots (Btor* btor,
                           BtorIntHashTable* roots,
                           BtorNode* exp,
                           BtorBitVector* bv)
{
  assert (btor);
  assert (roots);
  assert (exp);
  assert (BTOR_IS_REGULAR_NODE (exp));
  assert (bv);
  assert (btor_compare_bv (btor_get_bv_model (btor, exp), bv));

  (void) btor;

  /* exp: old assignment = 0, new assignment = 1 -> bv = 1
   *      -> remove */
  if (btor_get_int_hash_map (roots, exp->id))
  {
    btor_remove_int_hash_map (roots, exp->id, 0);
    assert (btor_is_false_bv (btor_get_bv_model (btor, exp)));
    assert (btor_is_true_bv (bv));
  }
  /* -exp: old assignment = 0, new assignment = 1 -> bv = 0
   * -> remove */
  else if (btor_get_int_hash_map (roots, -exp->id))
  {
    btor_remove_int_hash_map (roots, -exp->id, 0);
    assert (
        btor_is_false_bv (btor_get_bv_model (btor, BTOR_INVERT_NODE (exp))));
    assert (btor_is_false_bv (bv));
  }
  /* exp: old assignment = 1, new assignment = 0 -> bv = 0
   * -> add */
  else if (btor_is_false_bv (bv))
  {
    btor_add_int_hash_map (roots, exp->id);
    assert (btor_is_true_bv (btor_get_bv_model (btor, exp)));
  }
  /* -exp: old assignment = 1, new assignment = 0 -> bv = 1
   * -> add */
  else
  {
    assert (btor_is_true_bv (bv));
    btor_add_int_hash_map (roots, -exp->id);
    assert (btor_is_true_bv (btor_get_bv_model (btor, BTOR_INVERT_NODE (exp))));
  }
}

void btor_propsls_update_cone (Btor* btor,
                               BtorIntHashTable* roots,
                               BtorPtrHashTable* score,
                               BtorIntHashTable* exps,
                               BtorBitVector* assignment,
                               uint64_t* stats_updates,
                               double* time_update_cone,
                               double* time_update_cone_reset,
                               double* time_update_cone_model_gen,
                               double* time_update_cone_compute_score);

#endif
