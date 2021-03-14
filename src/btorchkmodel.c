/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2012-2020 Mathias Preiner.
 *  Copyright (C) 2012-2019 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btorchkmodel.h"

#include "btorabort.h"
#include "btorclone.h"
#include "btorcore.h"
#include "btorexp.h"
#include "btorlog.h"
#include "btormodel.h"
#include "btoropt.h"
#include "btorsubst.h"
#include "preprocess/btorpreprocess.h"
#include "preprocess/btorvarsubst.h"
#include "utils/btorhashptr.h"
#include "utils/btorutil.h"

struct BtorCheckModelContext
{
  Btor *btor;
  Btor *clone;
  BtorPtrHashTable *inputs;
};

static BtorPtrHashTable *
map_inputs (Btor *btor, Btor *clone)
{
  assert (btor);
  assert (clone);

  BtorNode *cur;
  BtorPtrHashBucket *b;
  BtorPtrHashTableIterator it;
  BtorPtrHashTable *inputs;

  inputs = btor_hashptr_table_new (clone->mm,
                                   (BtorHashPtr) btor_node_hash_by_id,
                                   (BtorCmpPtr) btor_node_compare_by_id);

  btor_iter_hashptr_init (&it, clone->bv_vars);
  while (btor_iter_hashptr_has_next (&it))
  {
    cur = btor_iter_hashptr_next (&it);
    b   = btor_hashptr_table_get (btor->bv_vars, cur);
    assert (b);

    assert (!btor_hashptr_table_get (inputs, cur));
    btor_hashptr_table_add (inputs, btor_node_copy (clone, cur))->data.as_ptr =
        btor_node_copy (btor, (BtorNode *) b->key);
  }

  btor_iter_hashptr_init (&it, clone->ufs);
  while (btor_iter_hashptr_has_next (&it))
  {
    cur = btor_iter_hashptr_next (&it);
    b   = btor_hashptr_table_get (btor->ufs, cur);
    assert (b);

    assert (!btor_hashptr_table_get (inputs, cur));
    btor_hashptr_table_add (inputs, btor_node_copy (clone, cur))->data.as_ptr =
        btor_node_copy (btor, (BtorNode *) b->key);
  }

  return inputs;
}

static void
rebuild_formula (Btor *btor, uint32_t rewrite_level)
{
  assert (btor);

  uint32_t i, cnt;
  BtorNode *cur;
  BtorPtrHashTable *t;

  BTORLOG (1, "rebuild formula with rewrite level %u", rewrite_level);

  /* set new rewrite level */
  btor_opt_set (btor, BTOR_OPT_REWRITE_LEVEL, rewrite_level);

  t = btor_hashptr_table_new (btor->mm,
                              (BtorHashPtr) btor_node_hash_by_id,
                              (BtorCmpPtr) btor_node_compare_by_id);

  /* collect all leaves and rebuild whole formula */
  for (i = 1, cnt = BTOR_COUNT_STACK (btor->nodes_id_table); i <= cnt; i++)
  {
    if (!(cur = BTOR_PEEK_STACK (btor->nodes_id_table, cnt - i))) continue;

    if (btor_node_is_simplified (cur)) continue;

    if (cur->arity == 0)
    {
      assert (btor_node_is_bv_var (cur) || btor_node_is_bv_const (cur)
              || btor_node_is_param (cur) || btor_node_is_uf (cur));
      btor_hashptr_table_add (t, cur);
    }
  }

  btor_substitute_and_rebuild (btor, t);
  btor_hashptr_table_delete (t);

  BTORLOG (1, "rebuild formula done");
}

void
btor_check_model (BtorCheckModelContext *ctx)
{
  assert (ctx);

  uint32_t i;
  int32_t ret;
  Btor *btor, *clone;
  BtorNode *cur, *exp, *simp, *simp_clone, *real_simp_clone, *model, *eq;
  BtorNode *args, *apply;
  BtorPtrHashTableIterator it;
  const BtorPtrHashTable *fmodel;
  BtorBitVector *value;
  BtorBitVectorTuple *args_tuple;
  BtorNodePtrStack consts;

  btor = ctx->btor;

  BTORLOG (1, "start check model");

  assert (btor->last_sat_result == BTOR_RESULT_SAT);
  clone = ctx->clone;

  if (!btor_opt_get (btor, BTOR_OPT_MODEL_GEN))
  {
    switch (btor_opt_get (btor, BTOR_OPT_ENGINE))
    {
      case BTOR_ENGINE_SLS:
      case BTOR_ENGINE_PROP:
      case BTOR_ENGINE_AIGPROP:
        btor->slv->api.generate_model (btor->slv, false, false);
        break;
      default: btor->slv->api.generate_model (btor->slv, false, true);
    }
  }

  /* Reset terminate callbacks. */
  clone->cbs.term.fun   = 0;
  clone->cbs.term.state = 0;
  clone->cbs.term.done  = 0;

  /* formula did not change since last sat call, we have to reset assumptions
   * from the previous run */
  if (clone->valid_assignments) btor_reset_incremental_usage (clone);

  /* add assumptions as assertions */
  btor_iter_hashptr_init (&it, clone->assumptions);
  while (btor_iter_hashptr_has_next (&it))
    btor_assert_exp (clone, btor_iter_hashptr_next (&it));
  btor_reset_assumptions (clone);

  /* clone->assertions have been already added at this point. */
  while (!BTOR_EMPTY_STACK (clone->assertions))
  {
    cur = BTOR_POP_STACK (clone->assertions);
    btor_node_release (clone, cur);
  }

  /* apply variable substitution until fixpoint */
  while (clone->varsubst_constraints->count > 0)
  {
    btor_substitute_var_exps (clone);
  }

  /* rebuild formula with new rewriting level */
  rebuild_formula (clone, 3);

  /* add bit vector variable models */
  BTOR_INIT_STACK (clone->mm, consts);
  btor_iter_hashptr_init (&it, ctx->inputs);
  while (btor_iter_hashptr_has_next (&it))
  {
    exp = (BtorNode *) it.bucket->data.as_ptr;
    assert (exp);
    assert (btor_node_is_regular (exp));
    assert (exp->btor == btor);
    /* Note: we do not want simplified constraints here */
    simp = btor_node_get_simplified (btor, exp);
    cur  = btor_iter_hashptr_next (&it);
    assert (btor_node_is_regular (cur));
    assert (cur->btor == clone);
    simp_clone      = btor_simplify_exp (clone, cur);
    real_simp_clone = btor_node_real_addr (simp_clone);

    if (btor_node_is_fun (real_simp_clone))
    {
      fmodel = btor_model_get_fun (btor, simp);
      if (!fmodel) continue;

      BTORLOG (
          2, "assert model for %s", btor_util_node2string (real_simp_clone));
      btor_iter_hashptr_init (&it, (BtorPtrHashTable *) fmodel);
      while (btor_iter_hashptr_has_next (&it))
      {
        value      = (BtorBitVector *) it.bucket->data.as_ptr;
        args_tuple = btor_iter_hashptr_next (&it);

        /* Ignore default values of constant arrays */
        if (!args_tuple->arity) continue;

        /* create condition */
        assert (BTOR_EMPTY_STACK (consts));
        for (i = 0; i < args_tuple->arity; i++)
        {
          model = btor_exp_bv_const (clone, args_tuple->bv[i]);
          BTOR_PUSH_STACK (consts, model);
          BTORLOG (2, "  arg%u: %s", i, btor_util_node2string(model));
        }

        args  = btor_exp_args (clone, consts.start, BTOR_COUNT_STACK (consts));
        apply = btor_exp_apply (clone, real_simp_clone, args);
        model = btor_exp_bv_const (clone, value);
        eq    = btor_exp_eq (clone, apply, model);

        BTORLOG (2, "  value: %s", btor_util_node2string(model));

        btor_assert_exp (clone, eq);
        btor_node_release (clone, eq);
        btor_node_release (clone, model);
        btor_node_release (clone, apply);
        btor_node_release (clone, args);

        while (!BTOR_EMPTY_STACK (consts))
          btor_node_release (clone, BTOR_POP_STACK (consts));
      }
    }
    else
    {
      /* we need to invert the assignment if simplified is inverted */
      model = btor_exp_bv_const (
          clone,
          (BtorBitVector *) btor_model_get_bv (
              btor, btor_node_cond_invert (simp_clone, simp)));
      BTORLOG (2,
               "assert model for %s (%s) [%s]",
               btor_util_node2string (real_simp_clone),
               btor_node_get_symbol (clone, cur),
               btor_util_node2string (model));

      eq = btor_exp_eq (clone, real_simp_clone, model);
      btor_assert_exp (clone, eq);
      btor_node_release (clone, eq);
      btor_node_release (clone, model);
    }
  }
  BTOR_RELEASE_STACK (consts);

  /* apply variable substitution until fixpoint */
  while (clone->varsubst_constraints->count > 0)
    btor_substitute_var_exps (clone);

  btor_opt_set (clone, BTOR_OPT_BETA_REDUCE, BTOR_BETA_REDUCE_ALL);
  ret = btor_simplify (clone);

  // btor_print_model (btor, "btor", stdout);
  assert (ret != BTOR_RESULT_UNKNOWN
          || btor_check_sat (clone, -1, -1) == BTOR_RESULT_SAT);
  // TODO: check if roots have been simplified through aig rewriting
  // BTOR_ABORT (ret == BTOR_RESULT_UNKNOWN, "rewriting needed");
  BTOR_ABORT (ret == BTOR_RESULT_UNSAT, "invalid model");
  BTORLOG (1, "end check model");
}

BtorCheckModelContext *
btor_check_model_init (Btor *btor)
{
  BtorCheckModelContext *ctx;

  BTOR_CNEW (btor->mm, ctx);

  ctx->btor  = btor;
  ctx->clone = btor_clone_exp_layer (btor, 0, true);
  btor_set_msg_prefix (ctx->clone, "chkm");
  btor_opt_set (ctx->clone, BTOR_OPT_FUN_DUAL_PROP, 0);
  btor_opt_set (ctx->clone, BTOR_OPT_CHK_UNCONSTRAINED, 0);
  btor_opt_set (ctx->clone, BTOR_OPT_CHK_MODEL, 0);
  btor_opt_set (ctx->clone, BTOR_OPT_CHK_FAILED_ASSUMPTIONS, 0);
  btor_opt_set (ctx->clone, BTOR_OPT_PRINT_DIMACS, 0);
  btor_set_term (ctx->clone, 0, 0);

  btor_opt_set (ctx->clone, BTOR_OPT_ENGINE, BTOR_ENGINE_FUN);
  if (ctx->clone->slv)
  {
    ctx->clone->slv->api.delet (ctx->clone->slv);
    ctx->clone->slv = 0;
  }

  ctx->inputs = map_inputs (btor, ctx->clone);

  return ctx;
}

void
btor_check_model_delete (BtorCheckModelContext *ctx)
{
  BtorPtrHashTableIterator it;
  btor_iter_hashptr_init (&it, ctx->inputs);
  while (btor_iter_hashptr_has_next (&it))
  {
    btor_node_release (ctx->btor, (BtorNode *) it.bucket->data.as_ptr);
    btor_node_release (ctx->clone, btor_iter_hashptr_next (&it));
  }
  btor_hashptr_table_delete (ctx->inputs);
  btor_delete (ctx->clone);
  BTOR_DELETE (ctx->btor->mm, ctx);
}
