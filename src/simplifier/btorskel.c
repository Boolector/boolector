/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2014 Armin Biere.
 *  Copyright (C) 2012-2017 Mathias Preiner.
 *  Copyright (C) 2012-2017 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifdef BTOR_USE_LINGELING
#include "simplifier/btorskel.h"
#include "btorcore.h"
#include "btordbg.h"
#include "utils/btorhashint.h"
#include "utils/btorutil.h"

#include "lglib.h"

static int32_t
fixed_exp (Btor *btor, BtorNode *exp)
{
  BtorNode *real_exp;
  BtorSATMgr *smgr;
  BtorAIG *aig;
  int32_t res, id;

  real_exp = btor_node_real_addr (exp);
  assert (btor_node_bv_get_width (btor, real_exp) == 1);
  if (!btor_node_is_synth (real_exp)) return 0;
  assert (real_exp->av);
  assert (real_exp->av->width == 1);
  assert (real_exp->av->aigs);
  aig = real_exp->av->aigs[0];
  if (aig == BTOR_AIG_TRUE)
    res = 1;
  else if (aig == BTOR_AIG_FALSE)
    res = -1;
  else
  {
    id = btor_aig_get_cnf_id (aig);
    if (!id) return 0;
    smgr = btor_get_sat_mgr (btor);
    res  = btor_sat_fixed (smgr, id);
  }
  if (btor_node_is_inverted (exp)) res = -res;
  return res;
}

static int32_t
process_skeleton_tseitin_lit (BtorPtrHashTable *ids, BtorNode *exp)
{
  BtorPtrHashBucket *b;
  BtorNode *real_exp;
  int32_t res;

  real_exp = btor_node_real_addr (exp);
  assert (btor_node_bv_get_width (real_exp->btor, real_exp) == 1);
  b = btor_hashptr_table_get (ids, real_exp);
  if (!b)
  {
    b              = btor_hashptr_table_add (ids, real_exp);
    b->data.as_int = (int32_t) ids->count;
  }

  res = b->data.as_int;
  assert (res > 0);

  if (btor_node_is_inverted (exp)) res = -res;

  return res;
}

static void
process_skeleton_tseitin (Btor *btor,
                          LGL *lgl,
                          BtorNodePtrStack *work_stack,
                          BtorIntHashTable *mark,
                          BtorPtrHashTable *ids,
                          BtorNode *root)
{
  assert (btor);

  int32_t i, lhs, rhs[3], fixed;
  BtorNode *exp;
  BtorHashTableData *d;

  BTOR_PUSH_STACK (*work_stack, root);

  do
  {
    exp = BTOR_POP_STACK (*work_stack);
    assert (exp);
    exp = btor_node_real_addr (exp);
    d   = btor_hashint_map_get (mark, exp->id);

    if (!d)
    {
      btor_hashint_map_add (mark, exp->id);

      BTOR_PUSH_STACK (*work_stack, exp);
      for (i = exp->arity - 1; i >= 0; i--)
        BTOR_PUSH_STACK (*work_stack, exp->e[i]);
    }
    else if (d->as_int == 0)
    {
      d->as_int = 1;
      if (btor_node_is_fun (exp) || btor_node_is_args (exp)
          || exp->parameterized || btor_node_bv_get_width (btor, exp) != 1)
        continue;

#ifndef NDEBUG
      BtorNode *child;
      for (i = 0; i < exp->arity; i++)
      {
        child = btor_node_real_addr (exp->e[i]);
        d     = btor_hashint_map_get (mark, child->id);
        assert (d->as_int == 1);
        if (!btor_node_is_fun (child) && !btor_node_is_args (child)
            && !child->parameterized
            && btor_node_bv_get_width (btor, child) == 1)
          assert (btor_hashptr_table_get (ids, child));
      }
#endif
      lhs   = process_skeleton_tseitin_lit (ids, exp);
      fixed = fixed_exp (btor, exp);
      if (fixed)
      {
        lgladd (lgl, (fixed > 0) ? lhs : -lhs);
        lgladd (lgl, 0);
      }

      switch (exp->kind)
      {
        case BTOR_BV_AND_NODE:
          rhs[0] = process_skeleton_tseitin_lit (ids, exp->e[0]);
          rhs[1] = process_skeleton_tseitin_lit (ids, exp->e[1]);

          lgladd (lgl, -lhs);
          lgladd (lgl, rhs[0]);
          lgladd (lgl, 0);

          lgladd (lgl, -lhs);
          lgladd (lgl, rhs[1]);
          lgladd (lgl, 0);

          lgladd (lgl, lhs);
          lgladd (lgl, -rhs[0]);
          lgladd (lgl, -rhs[1]);
          lgladd (lgl, 0);
          break;

        case BTOR_BV_EQ_NODE:
          if (btor_node_bv_get_width (btor, exp->e[0]) != 1) break;
          assert (btor_node_bv_get_width (btor, exp->e[1]) == 1);
          rhs[0] = process_skeleton_tseitin_lit (ids, exp->e[0]);
          rhs[1] = process_skeleton_tseitin_lit (ids, exp->e[1]);

          lgladd (lgl, -lhs);
          lgladd (lgl, -rhs[0]);
          lgladd (lgl, rhs[1]);
          lgladd (lgl, 0);

          lgladd (lgl, -lhs);
          lgladd (lgl, rhs[0]);
          lgladd (lgl, -rhs[1]);
          lgladd (lgl, 0);

          lgladd (lgl, lhs);
          lgladd (lgl, rhs[0]);
          lgladd (lgl, rhs[1]);
          lgladd (lgl, 0);

          lgladd (lgl, lhs);
          lgladd (lgl, -rhs[0]);
          lgladd (lgl, -rhs[1]);
          lgladd (lgl, 0);

          break;

#if 0
	    // can not happen, skeleton preprocessing is enabled when
	    // rewrite level > 2, Boolean condition are rewritten when
	    // rewrite level > 0
	    case BTOR_COND_NODE:
	      assert (btor_node_bv_get_width (btor, exp->e[0]) == 1);
	      if (btor_node_bv_get_width (btor, exp->e[1]) != 1)
		break;
	      assert (btor_node_bv_get_width (btor, exp->e[2]) == 1);
	      rhs[0] = process_skeleton_tseitin_lit (ids, exp->e[0]);
	      rhs[1] = process_skeleton_tseitin_lit (ids, exp->e[1]);
	      rhs[2] = process_skeleton_tseitin_lit (ids, exp->e[2]);

	      lgladd (lgl, -lhs);
	      lgladd (lgl, -rhs[0]);
	      lgladd (lgl, rhs[1]);
	      lgladd (lgl, 0);

	      lgladd (lgl, -lhs);
	      lgladd (lgl, rhs[0]);
	      lgladd (lgl, rhs[2]);
	      lgladd (lgl, 0);

	      lgladd (lgl, lhs);
	      lgladd (lgl, -rhs[0]);
	      lgladd (lgl, -rhs[1]);
	      lgladd (lgl, 0);

	      lgladd (lgl, lhs);
	      lgladd (lgl, rhs[0]);
	      lgladd (lgl, -rhs[2]);
	      lgladd (lgl, 0);
	      break;
#endif

        default:
          assert (!btor_node_is_cond (exp));
          assert (!btor_node_is_proxy (exp));
          break;
      }
    }
  } while (!BTOR_EMPTY_STACK (*work_stack));
}

void
btor_process_skeleton (Btor *btor)
{
  BtorPtrHashTable *ids;
  uint32_t count, fixed;
  BtorNodePtrStack work_stack;
  BtorMemMgr *mm = btor->mm;
  BtorPtrHashTableIterator it;
  double start, delta;
  int32_t res, lit, val;
  BtorNode *exp;
  LGL *lgl;
  BtorIntHashTable *mark;

  start = btor_util_time_stamp ();

  ids = btor_hashptr_table_new (mm,
                                (BtorHashPtr) btor_node_hash_by_id,
                                (BtorCmpPtr) btor_node_compare_by_id);

  lgl = lglinit ();
  lglsetprefix (lgl, "[lglskel] ");

  if (btor_opt_get (btor, BTOR_OPT_VERBOSITY) >= 2)
  {
    lglsetopt (lgl, "verbose", btor_opt_get (btor, BTOR_OPT_VERBOSITY) - 1);
    lglbnr ("Lingeling", "[lglskel] ", stdout);
    fflush (stdout);
  }
  else
    lglsetopt (lgl, "verbose", -1);

  count = 0;

  BTOR_INIT_STACK (mm, work_stack);
  mark = btor_hashint_map_new (mm);

  btor_iter_hashptr_init (&it, btor->synthesized_constraints);
  btor_iter_hashptr_queue (&it, btor->unsynthesized_constraints);
  while (btor_iter_hashptr_has_next (&it))
  {
    count++;
    exp = btor_iter_hashptr_next (&it);
    assert (btor_node_bv_get_width (btor, exp) == 1);
    process_skeleton_tseitin (btor, lgl, &work_stack, mark, ids, exp);
    lgladd (lgl, process_skeleton_tseitin_lit (ids, exp));
    lgladd (lgl, 0);
  }

  BTOR_RELEASE_STACK (work_stack);
  btor_hashint_map_delete (mark);

  BTOR_MSG (btor->msg,
            1,
            "found %u skeleton literals in %u constraints",
            ids->count,
            count);

  res = lglsimp (lgl, 0);

  if (btor_opt_get (btor, BTOR_OPT_VERBOSITY))
  {
    BTOR_MSG (btor->msg, 1, "skeleton preprocessing result %d", res);
    lglstats (lgl);
  }

  fixed = 0;

  if (res == 20)
  {
    BTOR_MSG (btor->msg, 1, "skeleton inconsistent");
    btor->inconsistent = true;
  }
  else
  {
    assert (res == 0 || res == 10);
    btor_iter_hashptr_init (&it, ids);
    while (btor_iter_hashptr_has_next (&it))
    {
      exp = btor_iter_hashptr_next (&it);
      assert (!btor_node_is_inverted (exp));
      lit = process_skeleton_tseitin_lit (ids, exp);
      val = lglfixed (lgl, lit);
      if (val)
      {
        if (val < 0) exp = btor_node_invert (exp);
        if (!btor_hashptr_table_get (btor->synthesized_constraints, exp)
            && !btor_hashptr_table_get (btor->unsynthesized_constraints, exp))
        {
          btor_assert_exp (btor, exp);
          btor->stats.skeleton_constraints++;
          fixed++;
        }
      }
      else
      {
        assert (!btor_hashptr_table_get (btor->synthesized_constraints, exp));
        assert (!btor_hashptr_table_get (btor->unsynthesized_constraints, exp));
      }
    }
  }

  btor_hashptr_table_delete (ids);
  lglrelease (lgl);

  delta = btor_util_time_stamp () - start;
  btor->time.skel += delta;
  BTOR_MSG (
      btor->msg,
      1,
      "skeleton preprocessing produced %u new constraints in %.1f seconds",
      fixed,
      delta);
}
#endif
