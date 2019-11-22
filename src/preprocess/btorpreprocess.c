/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2017 Armin Biere.
 *  Copyright (C) 2012-2019 Mathias Preiner.
 *  Copyright (C) 2012-2019 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "preprocess/btorpreprocess.h"

#include "btorcore.h"
#include "btordbg.h"
#include "btorexp.h"
#include "btorlog.h"
#include "btorsubst.h"
#include "preprocess/btorack.h"
#include "preprocess/btorder.h"
#include "preprocess/btorelimapplies.h"
#include "preprocess/btorelimslices.h"
#include "preprocess/btorembed.h"
#include "preprocess/btorextract.h"
#include "preprocess/btormerge.h"
#include "preprocess/btornormadd.h"
#include "preprocess/btorunconstrained.h"
#include "preprocess/btorvarsubst.h"
#ifndef BTOR_DO_NOT_PROCESS_SKELETON
#include "preprocess/btorskel.h"
#endif
#include "utils/btorhashptr.h"
#include "utils/btornodeiter.h"
#include "utils/btorutil.h"

int32_t
btor_simplify (Btor *btor)
{
  assert (btor);

  BtorSolverResult result;
  uint32_t rounds;
  double start, delta;
#ifndef BTOR_DO_NOT_PROCESS_SKELETON
  uint32_t skelrounds = 0;
#endif

  rounds = 0;
  start  = btor_util_time_stamp ();

  if (btor->valid_assignments) btor_reset_incremental_usage (btor);

  if (btor->inconsistent) goto DONE;

  /* empty varsubst_constraints table if variable substitution was disabled
   * after adding variable substitution constraints (they are still in
   * unsynthesized_constraints).
   */
  if (btor_opt_get (btor, BTOR_OPT_VAR_SUBST) == 0
      && btor->varsubst_constraints->count > 0)
  {
    btor_delete_varsubst_constraints (btor);
    btor->varsubst_constraints =
        btor_hashptr_table_new (btor->mm,
                                (BtorHashPtr) btor_node_hash_by_id,
                                (BtorCmpPtr) btor_node_compare_by_id);
    // TODO: check if this is still valid, and if this is the case also clear
    //       var_substitutions and var_rhs?
  }

  do
  {
    rounds++;
    assert (btor_dbg_check_all_hash_tables_proxy_free (btor));
    assert (btor_dbg_check_all_hash_tables_simp_free (btor));
    assert (btor_dbg_check_unique_table_children_proxy_free (btor));
    if (btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 1)
    {
      if (btor_opt_get (btor, BTOR_OPT_VAR_SUBST))
      {
        btor_substitute_var_exps (btor);

        if (btor->inconsistent)
        {
          BTORLOG (1, "formula inconsistent after variable substitution");
          break;
        }

        if (btor->varsubst_constraints->count)
          break;  // TODO (ma): continue instead of break?
      }

      while (btor->embedded_constraints->count)
      {
        btor_process_embedded_constraints (btor);

        if (btor->inconsistent)
        {
          BTORLOG (1,
                   "formula inconsistent after embedded constraint processing");
          break;
        }
      }

      if (btor->varsubst_constraints->count) continue;
    }

    if (btor_opt_get (btor, BTOR_OPT_ELIMINATE_SLICES)
        && btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 2
        && !btor_opt_get (btor, BTOR_OPT_INCREMENTAL))
    {
      btor_eliminate_slices_on_bv_vars (btor);
      if (btor->inconsistent)
      {
        BTORLOG (1, "formula inconsistent after slice elimination");
        break;
      }

      if (btor->varsubst_constraints->count
          || btor->embedded_constraints->count)
        continue;
    }

#ifndef BTOR_DO_NOT_PROCESS_SKELETON
    if (btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 2
        && btor_opt_get (btor, BTOR_OPT_SKELETON_PREPROC))
    {
      skelrounds++;
      if (skelrounds <= 1)  // TODO only one?
      {
        btor_process_skeleton (btor);
        if (btor->inconsistent)
        {
          BTORLOG (1, "formula inconsistent after skeleton preprocessing");
          break;
        }
      }

      if (btor->varsubst_constraints->count
          || btor->embedded_constraints->count)
        continue;
    }
#endif

    if (btor->varsubst_constraints->count || btor->embedded_constraints->count)
      continue;

    if (btor_opt_get (btor, BTOR_OPT_UCOPT)
        && btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 2
        && !btor_opt_get (btor, BTOR_OPT_INCREMENTAL)
        && !btor_opt_get (btor, BTOR_OPT_MODEL_GEN))
    {
      btor_optimize_unconstrained (btor);
      if (btor->inconsistent)
      {
        BTORLOG (1, "formula inconsistent after skeleton preprocessing");
        break;
      }
    }

    if (btor->varsubst_constraints->count || btor->embedded_constraints->count)
      continue;

    if (btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 2
        && btor_opt_get (btor, BTOR_OPT_EXTRACT_LAMBDAS))
      btor_extract_lambdas (btor);

    if (btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 2
        && btor_opt_get (btor, BTOR_OPT_MERGE_LAMBDAS))
      btor_merge_lambdas (btor);

    if (btor->varsubst_constraints->count || btor->embedded_constraints->count)
      continue;

    /* rewrite/beta-reduce applies on lambdas */
    if (btor_opt_get (btor, BTOR_OPT_BETA_REDUCE))
    {
      /* If no UFs or function equalities are present, we eagerly eliminate all
       * remaining lambdas. */
      if (btor->ufs->count == 0 && btor->feqs->count == 0
          && !btor_opt_get (btor, BTOR_OPT_INCREMENTAL))
      {
        BTOR_MSG (btor->msg,
                  1,
                  "no UFs or function equalities, enable beta-reduction=all");
        btor_opt_set (btor, BTOR_OPT_BETA_REDUCE, BTOR_BETA_REDUCE_ALL);
      }
      btor_eliminate_applies (btor);
    }

    /* add ackermann constraints for all uninterpreted functions */
    if (btor_opt_get (btor, BTOR_OPT_ACKERMANN))
      btor_add_ackermann_constraints (btor);

    if (btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 2
        && btor_opt_get (btor, BTOR_OPT_SIMP_NORMAMLIZE_ADDERS))
      btor_normalize_adds (btor);

  } while (btor->varsubst_constraints->count
           || btor->embedded_constraints->count);

DONE:
  delta = btor_util_time_stamp () - start;
  btor->time.simplify += delta;
  BTOR_MSG (btor->msg, 1, "%u rewriting rounds in %.1f seconds", rounds, delta);

  if (btor->inconsistent)
  {
    BTORLOG (1, "formula inconsistent");
    result = BTOR_RESULT_UNSAT;
  }
  else if (btor->unsynthesized_constraints->count == 0u
           && btor->synthesized_constraints->count == 0u)
    result = BTOR_RESULT_SAT;
  else
    result = BTOR_RESULT_UNKNOWN;

  BTOR_MSG (btor->msg, 1, "simplification returned %d", result);
  return result;
}
