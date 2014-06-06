/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2014 Armin Biere.
 *  Copyright (C) 2012-2014 Mathias Preiner.
 *  Copyright (C) 2013-2014 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

/*------------------------------------------------------------------------*/

#include "boolector.h"
#include "btorabort.h"
#include "btorclone.h"
#include "btorconst.h"
#include "btorcore.h"
#include "btorexit.h"
#include "btorhash.h"
#include "btoriter.h"
#include "btorsort.h"
#include "btorutil.h"
#include "dumper/btordumpbtor.h"
#include "dumper/btordumpsmt.h"
#ifndef NDEBUG
#include "btorbitvec.h"
#endif

/*------------------------------------------------------------------------*/

#include <limits.h>
#include <stdio.h>
#include <string.h>

/*------------------------------------------------------------------------*/

#define BTOR_TRAPI_NODE_ID(exp) \
  (BTOR_IS_INVERTED_NODE (exp) ? -BTOR_REAL_ADDR_NODE (exp)->id : exp->id)

#define NODE_FMT " e%d"

#define BTOR_TRAPI(msg, args...)    \
  do                                \
  {                                 \
    if (!btor->apitrace) break;     \
    btor_trapi (btor, msg, ##args); \
  } while (0)

#define BTOR_TRAPI_UNFUN_EXT(name, exp, fmt, args...) \
  BTOR_TRAPI (name NODE_FMT " " fmt, BTOR_TRAPI_NODE_ID (exp), ##args)

#define BTOR_TRAPI_UNFUN(name, exp) \
  BTOR_TRAPI (name NODE_FMT, BTOR_TRAPI_NODE_ID (exp))

#define BTOR_TRAPI_BINFUN(name, e0, e1) \
  BTOR_TRAPI (name NODE_FMT NODE_FMT,   \
              BTOR_TRAPI_NODE_ID (e0),  \
              BTOR_TRAPI_NODE_ID (e1))

#define BTOR_TRAPI_TERFUN(name, e0, e1, e2)    \
  BTOR_TRAPI (name NODE_FMT NODE_FMT NODE_FMT, \
              BTOR_TRAPI_NODE_ID (e0),         \
              BTOR_TRAPI_NODE_ID (e1),         \
              BTOR_TRAPI_NODE_ID (e2))

#define BTOR_TRAPI_RETURN(res)     \
  do                               \
  {                                \
    BTOR_TRAPI ("return %d", res); \
  } while (0)

#define BTOR_TRAPI_RETURN_NODE(res)                           \
  do                                                          \
  {                                                           \
    BTOR_TRAPI ("return" NODE_FMT, BTOR_TRAPI_NODE_ID (res)); \
  } while (0)

#define BTOR_TRAPI_RETURN_PTR(res) \
  do                               \
  {                                \
    BTOR_TRAPI ("return %p", res); \
  } while (0)

#define BTOR_TRAPI_RETURN_STR(res) \
  do                               \
  {                                \
    BTOR_TRAPI ("return %s", res); \
  } while (0)

static void
btor_trapi (Btor *btor, const char *msg, ...)
{
  assert (btor);
  assert (btor->apitrace);

  va_list args;

  va_start (args, msg);
  vfprintf (btor->apitrace, msg, args);
  va_end (args);
  fputc ('\n', btor->apitrace);
  fflush (btor->apitrace);
}

static void
btor_open_apitrace (Btor *btor, const char *name)
{
  assert (btor);
  assert (name);

  FILE *file;
  char *cmd;
  int len = strlen (name);

  if (len >= 3 && !strcmp (name + len - 3, ".gz"))
  {
    len += 20;
    BTOR_NEWN (btor->mm, cmd, len);
    sprintf (cmd, "gzip -c > %s", name);
    if ((file = popen (cmd, "w"))) btor->closeapitrace = 2;
    BTOR_DELETEN (btor->mm, cmd, len);
  }
  else
  {
    if ((file = fopen (name, "w"))) btor->closeapitrace = 1;
  }

  if (file)
    btor->apitrace = file;
  else
    printf ("[boolector] WARNING failed to write API trace file to '%s'", name);
}

void
boolector_set_trapi (Btor *btor, FILE *apitrace)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_BOOLECTOR (btor->apitrace, "API trace already set");
  btor->apitrace = apitrace;
}

FILE *
boolector_get_trapi (Btor *btor)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  return btor->apitrace;
}

/*------------------------------------------------------------------------*/
#ifndef NDEBUG
/*------------------------------------------------------------------------*/

static void
btor_chkclone_mem (Btor *btor)
{
  assert (btor);
  assert (btor->clone);
  assert (btor->mm);
  assert (btor->clone->mm);
  assert (btor->mm->allocated == btor->clone->mm->allocated);
  assert (btor->mm->sat_allocated == btor->clone->mm->sat_allocated);
  /* Note: both maxallocated and sat_maxallocated may differ! */
}

#define BTOR_CHKCLONE_STATE(field)        \
  do                                      \
  {                                       \
    assert (clone->field == btor->field); \
  } while (0)

static void
btor_chkclone_state (Btor *btor)
{
  assert (btor);

  Btor *clone;

  clone = btor->clone;
  assert (clone);

  BTOR_CHKCLONE_STATE (dvn_id);
  BTOR_CHKCLONE_STATE (dan_id);
  BTOR_CHKCLONE_STATE (dpn_id);
  BTOR_CHKCLONE_STATE (rec_rw_calls);
  BTOR_CHKCLONE_STATE (rec_read_acond_calls);
  BTOR_CHKCLONE_STATE (valid_assignments);
  BTOR_CHKCLONE_STATE (vis_idx);
  BTOR_CHKCLONE_STATE (vread_index_id);
  BTOR_CHKCLONE_STATE (inconsistent);
  BTOR_CHKCLONE_STATE (found_constraint_false);
  BTOR_CHKCLONE_STATE (external_refs);
  BTOR_CHKCLONE_STATE (btor_sat_btor_called);
  BTOR_CHKCLONE_STATE (msgtick);
  BTOR_CHKCLONE_STATE (last_sat_result);
  BTOR_CHKCLONE_STATE (options.dual_prop);
  BTOR_CHKCLONE_STATE (options.just);
  BTOR_CHKCLONE_STATE (options.beta_reduce_all);
  BTOR_CHKCLONE_STATE (options.force_cleanup);
  BTOR_CHKCLONE_STATE (options.force_internal_cleanup);
  BTOR_CHKCLONE_STATE (options.generate_model_for_all_reads);
  BTOR_CHKCLONE_STATE (options.inc_enabled);
#ifndef NBTORLOG
  BTOR_CHKCLONE_STATE (options.loglevel);
#endif
  BTOR_CHKCLONE_STATE (options.model_gen);
  BTOR_CHKCLONE_STATE (options.pprint);
#ifndef BTOR_DO_NOT_OPTIMIZE_UNCONSTRAINED
  BTOR_CHKCLONE_STATE (options.ucopt);
#endif
  BTOR_CHKCLONE_STATE (options.rewrite_level);
  BTOR_CHKCLONE_STATE (options.simplify_constraints);
  BTOR_CHKCLONE_STATE (options.slice_propagation);
  BTOR_CHKCLONE_STATE (options.verbosity);
#ifdef BTOR_CHECK_FAILED
  BTOR_CHKCLONE_STATE (options.chk_failed_assumptions);
#endif
}

#define BTOR_CHKCLONE_STATS(field)                    \
  do                                                  \
  {                                                   \
    assert (clone->stats.field == btor->stats.field); \
  } while (0)

#define BTOR_CHKCLONE_CONSTRAINTSTATS(constraints, field)                     \
  do                                                                          \
  {                                                                           \
    assert (clone->stats.constraints.field == btor->stats.constraints.field); \
  } while (0)

static void
btor_chkclone_stats (Btor *btor)
{
  assert (btor);

  Btor *clone;

  clone = btor->clone;
  assert (clone);

  BTOR_CHKCLONE_STATS (max_rec_rw_calls);
  BTOR_CHKCLONE_STATS (lod_refinements);
  BTOR_CHKCLONE_STATS (synthesis_assignment_inconsistencies);
  BTOR_CHKCLONE_STATS (synthesis_inconsistency_apply);
  BTOR_CHKCLONE_STATS (synthesis_inconsistency_lambda);
  BTOR_CHKCLONE_STATS (function_congruence_conflicts);
  BTOR_CHKCLONE_STATS (beta_reduction_conflicts);
  BTOR_CHKCLONE_STATS (var_substitutions);
  BTOR_CHKCLONE_STATS (array_substitutions);
  BTOR_CHKCLONE_STATS (ec_substitutions);
  BTOR_CHKCLONE_STATS (vreads);
  BTOR_CHKCLONE_STATS (linear_equations);
  BTOR_CHKCLONE_STATS (gaussian_eliminations);
  BTOR_CHKCLONE_STATS (eliminated_slices);
  BTOR_CHKCLONE_STATS (skeleton_constraints);
  BTOR_CHKCLONE_STATS (adds_normalized);
  BTOR_CHKCLONE_STATS (ands_normalized);
  BTOR_CHKCLONE_STATS (muls_normalized);
  BTOR_CHKCLONE_STATS (read_props_construct);
  BTOR_CHKCLONE_STATS (lemmas_size_sum);
  BTOR_CHKCLONE_STATS (lclause_size_sum);

  BTOR_CHKCLONE_CONSTRAINTSTATS (constraints, varsubst);
  BTOR_CHKCLONE_CONSTRAINTSTATS (constraints, embedded);
  BTOR_CHKCLONE_CONSTRAINTSTATS (constraints, unsynthesized);
  BTOR_CHKCLONE_CONSTRAINTSTATS (constraints, synthesized);
  BTOR_CHKCLONE_CONSTRAINTSTATS (oldconstraints, varsubst);
  BTOR_CHKCLONE_CONSTRAINTSTATS (oldconstraints, embedded);
  BTOR_CHKCLONE_CONSTRAINTSTATS (oldconstraints, unsynthesized);
  BTOR_CHKCLONE_CONSTRAINTSTATS (oldconstraints, synthesized);

  BTOR_CHKCLONE_STATS (expressions);
  BTOR_CHKCLONE_STATS (beta_reduce_calls);
  BTOR_CHKCLONE_STATS (eval_exp_calls);
  BTOR_CHKCLONE_STATS (lambda_synth_apps);
  BTOR_CHKCLONE_STATS (lambdas_merged);
  BTOR_CHKCLONE_STATS (propagations);
  BTOR_CHKCLONE_STATS (propagations_down);
  BTOR_CHKCLONE_STATS (apply_props_construct);
}

#define BTOR_CHKCLONE_AIG(field)                   \
  do                                               \
  {                                                \
    assert (real_clone->field == real_aig->field); \
  } while (0)

#define BTOR_CHKCLONE_AIGPID(field)                        \
  do                                                       \
  {                                                        \
    if (!real_aig->field)                                  \
    {                                                      \
      assert (!real_clone->field);                         \
      break;                                               \
    }                                                      \
    assert (BTOR_IS_CONST_AIG (real_aig->field)            \
            || real_aig->field != real_clone->field);      \
    assert (real_aig->field->id == real_clone->field->id); \
  } while (0)

#define BTOR_CHKCLONE_AIGINV(field)                       \
  do                                                      \
  {                                                       \
    if (!real_aig->field)                                 \
    {                                                     \
      assert (!real_clone->field);                        \
      break;                                              \
    }                                                     \
    assert (BTOR_IS_INVERTED_AIG (real_aig->field)        \
            == BTOR_IS_INVERTED_AIG (real_clone->field)); \
    BTOR_CHKCLONE_AIGPID (field);                         \
  } while (0)

static void
btor_chkclone_aig (BtorAIG *aig, BtorAIG *clone)
{
  int i;
  BtorAIG *real_aig, *real_clone;

  real_aig   = BTOR_REAL_ADDR_AIG (aig);
  real_clone = BTOR_REAL_ADDR_AIG (clone);
  assert ((real_aig == BTOR_AIG_FALSE && real_clone == BTOR_AIG_FALSE)
          || real_aig != real_clone);

  if (real_aig != BTOR_AIG_FALSE)
  {
    BTOR_CHKCLONE_AIG (id);
    BTOR_CHKCLONE_AIG (refs);

    for (i = 0; i < 2; i++) BTOR_CHKCLONE_AIGINV (children[i]);

    BTOR_CHKCLONE_AIGPID (next);

    BTOR_CHKCLONE_AIG (cnf_id);
    BTOR_CHKCLONE_AIG (mark);
    BTOR_CHKCLONE_AIG (local);
  }
}

#define BTOR_CHKCLONE_AIG_UNIQUE_TABLE(table, clone)        \
  do                                                        \
  {                                                         \
    int i;                                                  \
    BtorAIG *next, *clone_next;                             \
    assert (table.size == clone.size);                      \
    assert (table.num_elements == clone.num_elements);      \
    for (i = 0; i < table.size; i++)                        \
    {                                                       \
      if (!table.chains[i])                                 \
      {                                                     \
        assert (!clone.chains[i]);                          \
        continue;                                           \
      }                                                     \
      btor_chkclone_aig (table.chains[i], clone.chains[i]); \
      next       = table.chains[i]->next;                   \
      clone_next = clone.chains[i]->next;                   \
      while (next)                                          \
      {                                                     \
        assert (clone_next);                                \
        btor_chkclone_aig (next, clone_next);               \
        next       = next->next;                            \
        clone_next = clone_next->next;                      \
      }                                                     \
      assert (!clone_next);                                 \
    }                                                       \
  } while (0)

#define BTOR_CHKCLONE_AIG_CNF_ID_TABLE(table, clone)               \
  do                                                               \
  {                                                                \
    int i;                                                         \
    assert (BTOR_COUNT_STACK (table) == 0);                        \
    assert (BTOR_COUNT_STACK (table) == BTOR_COUNT_STACK (clone)); \
    assert (BTOR_SIZE_STACK (table) == BTOR_SIZE_STACK (clone));   \
    for (i = 0; i < BTOR_SIZE_STACK (table); i++)                  \
    {                                                              \
      if (!table.start[i])                                         \
      {                                                            \
        assert (!clone.start[i]);                                  \
        continue;                                                  \
      }                                                            \
      assert (BTOR_IS_INVERTED_AIG (table.start[i])                \
              == BTOR_IS_INVERTED_AIG (clone.start[i]));           \
      assert (table.start[i] != clone.start[i]);                   \
      assert (table.start[i]->id == clone.start[i]->id);           \
    }                                                              \
  } while (0)

#define BTOR_CHKCLONE_EXP(field)                   \
  do                                               \
  {                                                \
    assert (real_exp->field == real_clone->field); \
  } while (0)

#define BTOR_CHKCLONE_EXPID(exp, clone)                                        \
  do                                                                           \
  {                                                                            \
    assert (BTOR_REAL_ADDR_NODE (exp)->id == BTOR_REAL_ADDR_NODE (clone)->id); \
  } while (0)

#define BTOR_CHKCLONE_EXPPID(field)                            \
  do                                                           \
  {                                                            \
    if (!real_exp->field)                                      \
    {                                                          \
      assert (!real_clone->field);                             \
      break;                                                   \
    }                                                          \
    assert (real_exp->field != real_clone->field);             \
    BTOR_CHKCLONE_EXPID (real_exp->field, real_clone->field);  \
    assert (BTOR_REAL_ADDR_NODE (real_exp->field)->btor->clone \
            == BTOR_REAL_ADDR_NODE (real_clone->field)->btor); \
  } while (0)

#define BTOR_CHKCLONE_EXPPINV(field)                       \
  do                                                       \
  {                                                        \
    BTOR_CHKCLONE_EXPPID (field);                          \
    assert (BTOR_IS_INVERTED_NODE (real_exp->field)        \
            == BTOR_IS_INVERTED_NODE (real_clone->field)); \
  } while (0)

#define BTOR_CHKCLONE_EXPPTAG(field)                   \
  do                                                   \
  {                                                    \
    BTOR_CHKCLONE_EXPPID (field);                      \
    assert (BTOR_GET_TAG_NODE (real_exp->field)        \
            == BTOR_GET_TAG_NODE (real_clone->field)); \
  } while (0)

/* Note: no hash table to be cloned uses data->asInt (check data->asPtr only) */
#define BTOR_CHKCLONE_NODE_PTR_HASH_TABLE(table, clone)                  \
  do                                                                     \
  {                                                                      \
    BtorPtrHashBucket *bb, *cbb;                                         \
    if (!(table))                                                        \
    {                                                                    \
      assert (!(clone));                                                 \
      break;                                                             \
    }                                                                    \
    assert ((table)->size == (clone)->size);                             \
    assert ((table)->count == (clone)->count);                           \
    assert ((table)->hash == (clone)->hash);                             \
    assert ((table)->cmp == (clone)->cmp);                               \
    for (bb = (table)->first, cbb = (clone)->first; bb;                  \
         bb = bb->next, cbb = cbb->next)                                 \
    {                                                                    \
      assert (cbb);                                                      \
      BTOR_CHKCLONE_EXPID ((BtorNode *) bb->key, (BtorNode *) cbb->key); \
      assert (!bb->next || cbb->next);                                   \
    }                                                                    \
  } while (0)

static void
btor_chkclone_exp (BtorNode *exp, BtorNode *clone)
{
  assert (exp);
  assert (clone);
  assert (exp != clone);
  assert ((!BTOR_IS_INVERTED_NODE (exp) && !BTOR_IS_INVERTED_NODE (clone))
          || (BTOR_IS_INVERTED_NODE (exp) && BTOR_IS_INVERTED_NODE (clone)));

  int i, len;
  BtorNode *real_exp, *real_clone, *e, *ce;
  BtorPtrHashBucket *b, *cb;

  real_exp   = BTOR_REAL_ADDR_NODE (exp);
  real_clone = BTOR_REAL_ADDR_NODE (clone);
  assert (real_exp != real_clone);
  assert (real_exp->id == real_clone->id);
  assert (real_exp->btor->clone == real_clone->btor);

  BTOR_CHKCLONE_EXP (kind);
  BTOR_CHKCLONE_EXP (mark);
  BTOR_CHKCLONE_EXP (aux_mark);
  BTOR_CHKCLONE_EXP (fun_mark);
  BTOR_CHKCLONE_EXP (beta_mark);
  BTOR_CHKCLONE_EXP (eval_mark);
  BTOR_CHKCLONE_EXP (synth_mark);
  BTOR_CHKCLONE_EXP (reachable);
  BTOR_CHKCLONE_EXP (tseitin);
  BTOR_CHKCLONE_EXP (lazy_tseitin);
  BTOR_CHKCLONE_EXP (vread);
  BTOR_CHKCLONE_EXP (vread_index);
  BTOR_CHKCLONE_EXP (constraint);
  BTOR_CHKCLONE_EXP (erased);
  BTOR_CHKCLONE_EXP (disconnected);
  BTOR_CHKCLONE_EXP (unique);
  BTOR_CHKCLONE_EXP (bytes);
  BTOR_CHKCLONE_EXP (parameterized);
  BTOR_CHKCLONE_EXP (lambda_below);
  BTOR_CHKCLONE_EXP (merge);
  BTOR_CHKCLONE_EXP (is_write);
  BTOR_CHKCLONE_EXP (is_read);

  if (real_exp->bits)
  {
    len = strlen (real_exp->bits);
    assert ((size_t) len == strlen (real_clone->bits));
    for (i = 0; i < len; i++) assert (real_exp->bits[i] == real_clone->bits[i]);
  }
  else
  {
    assert ((real_exp->av && real_clone->av)
            || (!real_exp->av && !real_clone->av));
  }

  BTOR_CHKCLONE_EXP (id);
  BTOR_CHKCLONE_EXP (len);
  BTOR_CHKCLONE_EXP (refs);
  BTOR_CHKCLONE_EXP (ext_refs);
  BTOR_CHKCLONE_EXP (parents);
  BTOR_CHKCLONE_EXP (arity);

  if (!BTOR_IS_FUN_NODE (real_exp))
  {
    if (real_exp->av)
    {
      assert (real_exp->av->len == real_clone->av->len);
      for (i = 0; i < real_exp->len; i++)
        btor_chkclone_aig (real_exp->av->aigs[i], real_clone->av->aigs[i]);
    }
    else
      assert (real_exp->av == real_clone->av);
  }
  else if (real_exp->rho)
    BTOR_CHKCLONE_NODE_PTR_HASH_TABLE (real_exp->rho, real_clone->rho);

  BTOR_CHKCLONE_EXPPID (next);
  /* Note: parent node used during BFS only, pointer is not reset after bfs,
   *	   hence not cloned, do not check */
  BTOR_CHKCLONE_EXPPINV (simplified);
  assert (real_exp->btor->clone == real_clone->btor);
  BTOR_CHKCLONE_EXPPTAG (first_parent);
  BTOR_CHKCLONE_EXPPTAG (last_parent);

  if (BTOR_IS_PROXY_NODE (real_exp)) return;

  if (!BTOR_IS_BV_CONST_NODE (real_exp))
  {
    assert (!real_clone->symbol
            || !strcmp (real_exp->symbol, real_clone->symbol));

    if (!BTOR_IS_BV_VAR_NODE (real_exp) && !BTOR_IS_ARRAY_VAR_NODE (real_exp)
        && !BTOR_IS_PARAM_NODE (real_exp))
    {
      if (real_exp->arity)
      {
        for (i = 0; i < real_exp->arity; i++) BTOR_CHKCLONE_EXPPINV (e[i]);
      }
      else
      {
        BTOR_CHKCLONE_EXP (upper);
        if (!BTOR_IS_ARRAY_EQ_NODE (real_exp))
          BTOR_CHKCLONE_EXP (lower);
        else
        {
          assert (real_exp->vreads->exp1->id == real_clone->vreads->exp1->id);
          assert (real_exp->vreads->exp2->id == real_clone->vreads->exp2->id);
        }
      }
    }

    for (i = 0; i < real_exp->arity; i++)
    {
      BTOR_CHKCLONE_EXPPTAG (prev_parent[i]);
      BTOR_CHKCLONE_EXPPTAG (next_parent[i]);
    }
  }

#if 0
  if (BTOR_IS_FUN_NODE (real_exp))
    {
      BTOR_CHKCLONE_EXP (index_len);
      BTOR_CHKCLONE_EXPPTAG (first_aeq_acond_parent);
      BTOR_CHKCLONE_EXPPTAG (last_aeq_acond_parent);

      if (!BTOR_IS_ARRAY_VAR_NODE (real_exp))
	{
	  for (i = 0; i < real_exp->arity; i++)
	    {
	      BTOR_CHKCLONE_EXPPTAG (prev_aeq_acond_parent[i]);
	      BTOR_CHKCLONE_EXPPTAG (next_aeq_acond_parent[i]);
	    }
	}
    }
#endif

  if (BTOR_IS_PARAM_NODE (real_exp))
  {
    if (((BtorParamNode *) real_exp)->lambda_exp)
    {
      assert (((BtorParamNode *) real_exp)->lambda_exp
              != ((BtorParamNode *) real_clone)->lambda_exp);
      BTOR_CHKCLONE_EXPID (((BtorParamNode *) real_exp)->lambda_exp,
                           ((BtorParamNode *) real_clone)->lambda_exp);
    }
    else
      assert (!((BtorParamNode *) real_clone)->lambda_exp);

    if (((BtorParamNode *) real_exp)->assigned_exp)
    {
      assert (((BtorParamNode *) real_exp)->assigned_exp
              != ((BtorParamNode *) real_clone)->assigned_exp);
      BTOR_CHKCLONE_EXPID (((BtorParamNode *) real_exp)->assigned_exp,
                           ((BtorParamNode *) real_clone)->assigned_exp);
    }
    else
      assert (!((BtorParamNode *) real_clone)->assigned_exp);
  }

  if (BTOR_IS_ARGS_NODE (real_exp))
    assert (((BtorArgsNode *) real_exp)->num_args
            == ((BtorArgsNode *) real_clone)->num_args);

  if (BTOR_IS_LAMBDA_NODE (real_exp))
  {
    if (((BtorLambdaNode *) real_exp)->synth_apps)
    {
      for (b = ((BtorLambdaNode *) real_exp)->synth_apps->first,
          cb = ((BtorLambdaNode *) real_clone)->synth_apps->first;
           b;
           b = b->next, cb = cb->next)
      {
        e  = b->key;
        ce = cb->key;
        if (e)
        {
          assert (ce);
          assert (e != ce);
          BTOR_CHKCLONE_EXPID (e, ce);
        }
        else
          assert (!ce);
        assert (!b->next || cb->next);
      }
    }

    if (((BtorLambdaNode *) real_exp)->head)
    {
      assert (((BtorLambdaNode *) real_exp)->head
              != ((BtorLambdaNode *) real_clone)->head);
      BTOR_CHKCLONE_EXPID (((BtorLambdaNode *) real_exp)->head,
                           ((BtorLambdaNode *) real_clone)->head);
    }
    else
      assert (!((BtorLambdaNode *) real_clone)->head);

    if (((BtorLambdaNode *) real_exp)->body)
    {
      assert (((BtorLambdaNode *) real_exp)->body
              != ((BtorLambdaNode *) real_clone)->body);
      BTOR_CHKCLONE_EXPID (((BtorLambdaNode *) real_exp)->body,
                           ((BtorLambdaNode *) real_clone)->body);
    }
    else
      assert (!((BtorLambdaNode *) real_clone)->body);
  }
}

#define BTOR_CHKCLONE_NODE_PTR_STACK(stack, clone)                 \
  do                                                               \
  {                                                                \
    int i;                                                         \
    assert (BTOR_COUNT_STACK (stack) == BTOR_COUNT_STACK (clone)); \
    for (i = 0; i < BTOR_COUNT_STACK (stack); i++)                 \
    {                                                              \
      if (!BTOR_PEEK_STACK (stack, i))                             \
      {                                                            \
        assert (!BTOR_PEEK_STACK (clone, i));                      \
        continue;                                                  \
      }                                                            \
      BTOR_CHKCLONE_EXPID (BTOR_PEEK_STACK (stack, i),             \
                           BTOR_PEEK_STACK (clone, i));            \
    }                                                              \
  } while (0)

#define BTOR_CHKCLONE_NODE_ID_TABLE(stack, clone)                  \
  do                                                               \
  {                                                                \
    int i;                                                         \
    assert (BTOR_COUNT_STACK (stack) == BTOR_COUNT_STACK (clone)); \
    for (i = 0; i < BTOR_COUNT_STACK (stack); i++)                 \
    {                                                              \
      if (!BTOR_PEEK_STACK (stack, i))                             \
      {                                                            \
        assert (!BTOR_PEEK_STACK (clone, i));                      \
        continue;                                                  \
      }                                                            \
      btor_chkclone_exp (BTOR_PEEK_STACK (stack, i),               \
                         BTOR_PEEK_STACK (clone, i));              \
    }                                                              \
  } while (0)

/* Note: no need to check next pointers here as we catch all of them when
 *	 traversing through nodes id table. */
#define BTOR_CHKCLONE_NODE_UNIQUE_TABLE(table, clone)         \
  do                                                          \
  {                                                           \
    int i;                                                    \
    assert (table.size == clone.size);                        \
    assert (table.num_elements == clone.num_elements);        \
    for (i = 0; i < table.size; i++)                          \
    {                                                         \
      if (!table.chains[i])                                   \
      {                                                       \
        assert (!clone.chains[i]);                            \
        continue;                                             \
      }                                                       \
      BTOR_CHKCLONE_EXPID (table.chains[i], clone.chains[i]); \
    }                                                         \
  } while (0)

static void
btor_chkclone_assignment_lists (Btor *btor)
{
  BtorBVAssignment *bvass, *cbvass;
  BtorArrayAssignment *arrass, *carrass;
  char **ind, **val, **cind, **cval;
  int i;

  assert (btor->bv_assignments->count == btor->clone->bv_assignments->count);
  for (bvass = btor->bv_assignments->first,
      cbvass = btor->clone->bv_assignments->first;
       bvass;
       bvass = bvass->next, cbvass = cbvass->next)
  {
    assert (cbvass);
    assert (!strcmp (btor_get_bv_assignment_str (bvass),
                     btor_get_bv_assignment_str (cbvass)));
  }

  assert (btor->array_assignments->count
          == btor->clone->array_assignments->count);
  for (arrass = btor->array_assignments->first,
      carrass = btor->clone->array_assignments->first;
       arrass;
       arrass = arrass->next, carrass = carrass->next)
  {
    assert (carrass);
    assert (arrass->size == carrass->size);
    btor_get_array_assignment_indices_values (arrass, &ind, &val, arrass->size);
    btor_get_array_assignment_indices_values (
        carrass, &cind, &cval, carrass->size);
    for (i = 0; i < arrass->size; i++)
    {
      assert (!strcmp (ind[i], cind[i]));
      assert (!strcmp (val[i], cval[i]));
    }
  }
}

static void
btor_chkclone_tables (Btor *btor)
{
  BtorPtrHashBucket *b, *cb;
  BtorHashTableIterator it, cit;

  BTOR_CHKCLONE_NODE_PTR_HASH_TABLE (btor->bv_vars, btor->clone->bv_vars);
  BTOR_CHKCLONE_NODE_PTR_HASH_TABLE (btor->array_vars, btor->clone->array_vars);
  BTOR_CHKCLONE_NODE_PTR_HASH_TABLE (btor->lambdas, btor->clone->lambdas);
  BTOR_CHKCLONE_NODE_PTR_HASH_TABLE (btor->substitutions,
                                     btor->clone->substitutions);
  BTOR_CHKCLONE_NODE_PTR_HASH_TABLE (btor->lod_cache, btor->clone->lod_cache);
  BTOR_CHKCLONE_NODE_PTR_HASH_TABLE (btor->varsubst_constraints,
                                     btor->clone->varsubst_constraints);
  BTOR_CHKCLONE_NODE_PTR_HASH_TABLE (btor->embedded_constraints,
                                     btor->clone->embedded_constraints);
  BTOR_CHKCLONE_NODE_PTR_HASH_TABLE (btor->unsynthesized_constraints,
                                     btor->clone->unsynthesized_constraints);
  BTOR_CHKCLONE_NODE_PTR_HASH_TABLE (btor->synthesized_constraints,
                                     btor->clone->synthesized_constraints);
  BTOR_CHKCLONE_NODE_PTR_HASH_TABLE (btor->assumptions,
                                     btor->clone->assumptions);
  BTOR_CHKCLONE_NODE_PTR_HASH_TABLE (btor->var_rhs, btor->clone->var_rhs);
  BTOR_CHKCLONE_NODE_PTR_HASH_TABLE (btor->array_rhs, btor->clone->array_rhs);
  BTOR_CHKCLONE_NODE_PTR_HASH_TABLE (btor->cache, btor->clone->cache);

  if (btor->parameterized)
  {
    assert (btor->clone->parameterized);
    assert (btor->parameterized->size == btor->clone->parameterized->size);
    assert (btor->parameterized->count == btor->clone->parameterized->count);
    assert (btor->parameterized->hash == btor->clone->parameterized->hash);
    assert (btor->parameterized->cmp == btor->clone->parameterized->cmp);
    assert (!btor->parameterized->first || btor->clone->parameterized->first);
    for (b = btor->parameterized->first, cb = btor->clone->parameterized->first;
         b;
         b = b->next, cb = cb->next)
    {
      assert (cb);
      BTOR_CHKCLONE_EXPID ((BtorNode *) b->key, (BtorNode *) cb->key);
      BTOR_CHKCLONE_NODE_PTR_HASH_TABLE ((BtorPtrHashTable *) b->data.asPtr,
                                         (BtorPtrHashTable *) cb->data.asPtr);
      assert (!b->next || cb->next);
    }
  }
  else
    assert (!btor->clone->parameterized);

  if (btor->bv_model)
  {
    assert (btor->clone->bv_model);
    assert (btor->bv_model->size == btor->clone->bv_model->size);
    assert (btor->bv_model->count == btor->clone->bv_model->count);
    assert (btor->bv_model->hash == btor->clone->bv_model->hash);
    assert (btor->bv_model->cmp == btor->clone->bv_model->cmp);
    init_node_hash_table_iterator (&it, btor->bv_model);
    init_node_hash_table_iterator (&cit, btor->clone->bv_model);
    while (has_next_node_hash_table_iterator (&it))
    {
      assert (has_next_node_hash_table_iterator (&cit));
      BTOR_CHKCLONE_EXPID ((BtorNode *) it.cur, (BtorNode *) cit.cur);
      assert (it.bucket->data.asPtr);
      assert (cit.bucket->data.asPtr);
      assert (!btor_compare_bv ((BitVector *) it.bucket->data.asPtr,
                                (BitVector *) cit.bucket->data.asPtr));
      (void) next_node_hash_table_iterator (&it);
      (void) next_node_hash_table_iterator (&cit);
    }
    assert (!has_next_node_hash_table_iterator (&cit));
  }
  else
    assert (!btor->clone->bv_model);

  if (btor->array_model)
  {
    assert (btor->clone->array_model);
    assert (btor->array_model->size == btor->clone->array_model->size);
    assert (btor->array_model->count == btor->clone->array_model->count);
    assert (btor->array_model->hash == btor->clone->array_model->hash);
    assert (btor->array_model->cmp == btor->clone->array_model->cmp);
    for (b = btor->array_model->first, cb = btor->clone->array_model->first; b;
         b = b->next, cb = cb->next)
    {
      assert (cb);
      BTOR_CHKCLONE_EXPID ((BtorNode *) b->key, (BtorNode *) cb->key);
      assert (b->data.asPtr);
      assert (cb->data.asPtr);

      init_hash_table_iterator (&it, (BtorPtrHashTable *) b->data.asPtr);
      init_hash_table_iterator (&cit, (BtorPtrHashTable *) cb->data.asPtr);
      while (has_next_hash_table_iterator (&it))
      {
        assert (has_next_hash_table_iterator (&cit));
        assert (!btor_compare_bv ((BitVector *) it.bucket->data.asPtr,
                                  (BitVector *) cit.bucket->data.asPtr));
        assert (!btor_compare_bv_tuple ((BitVectorTuple *) it.cur,
                                        (BitVectorTuple *) cit.cur));
        (void) next_hash_table_iterator (&it);
        (void) next_hash_table_iterator (&cit);
      }
      assert (!has_next_hash_table_iterator (&cit));
      assert (!b->next || cb->next);
    }
  }
  else
    assert (!btor->clone->array_model);
}

#define BTOR_CHKCLONE()                                                \
  do                                                                   \
  {                                                                    \
    if (!btor->clone) break;                                           \
    btor_chkclone_mem (btor);                                          \
    btor_chkclone_state (btor);                                        \
    btor_chkclone_stats (btor);                                        \
    btor_chkclone_assignment_lists (btor);                             \
    BTOR_CHKCLONE_AIG_UNIQUE_TABLE (                                   \
        btor_get_aig_mgr_aigvec_mgr (btor->avmgr)->table,              \
        btor_get_aig_mgr_aigvec_mgr (btor->clone->avmgr)->table);      \
    BTOR_CHKCLONE_AIG_CNF_ID_TABLE (                                   \
        btor_get_aig_mgr_aigvec_mgr (btor->avmgr)->id2aig,             \
        btor_get_aig_mgr_aigvec_mgr (btor->clone->avmgr)->id2aig);     \
    BTOR_CHKCLONE_NODE_ID_TABLE (btor->nodes_id_table,                 \
                                 btor->clone->nodes_id_table);         \
    BTOR_CHKCLONE_NODE_UNIQUE_TABLE (btor->nodes_unique_table,         \
                                     btor->clone->nodes_unique_table); \
    BTOR_CHKCLONE_NODE_PTR_STACK (btor->arrays_with_model,             \
                                  btor->clone->arrays_with_model);     \
    btor_chkclone_tables (btor);                                       \
  } while (0)

#define BTOR_CHKCLONE_NORES(fun, args...)  \
  do                                       \
  {                                        \
    if (!btor->clone) break;               \
    boolector_##fun (btor->clone, ##args); \
    BTOR_CHKCLONE ();                      \
  } while (0)

#define BTOR_CHKCLONE_RES(res, fun, args...)              \
  do                                                      \
  {                                                       \
    if (!btor->clone) break;                              \
    int cloneres = boolector_##fun (btor->clone, ##args); \
    (void) cloneres;                                      \
    assert (cloneres == res);                             \
    BTOR_CHKCLONE ();                                     \
  } while (0)

#define BTOR_CHKCLONE_RES_PTR(res, fun, args...)                            \
  do                                                                        \
  {                                                                         \
    if (!btor->clone) break;                                                \
    BtorNode *cloneres =                                                    \
        BTOR_IMPORT_BOOLECTOR_NODE (boolector_##fun (btor->clone, ##args)); \
    (void) cloneres;                                                        \
    btor_chkclone_exp (res, cloneres);                                      \
    BTOR_CHKCLONE ();                                                       \
  } while (0)

#define BTOR_CHKCLONE_RES_STR(res, fun, args...)                  \
  do                                                              \
  {                                                               \
    if (!btor->clone) break;                                      \
    const char *cloneres = boolector_##fun (btor->clone, ##args); \
    (void) cloneres;                                              \
    assert (!strcmp (cloneres, res));                             \
    BTOR_CHKCLONE ();                                             \
  } while (0)

#define BTOR_CLONED_EXP(exp)                                                 \
  ((btor->clone ? BTOR_EXPORT_BOOLECTOR_NODE (                               \
                      BTOR_IS_INVERTED_NODE (exp)                            \
                          ? BTOR_INVERT_NODE (BTOR_PEEK_STACK (              \
                                btor->clone->nodes_id_table,                 \
                                BTOR_REAL_ADDR_NODE (exp)->id))              \
                          : BTOR_PEEK_STACK (btor->clone->nodes_id_table,    \
                                             BTOR_REAL_ADDR_NODE (exp)->id)) \
                : 0))

/*------------------------------------------------------------------------*/
#endif
/*------------------------------------------------------------------------*/

void
boolector_chkclone (Btor *btor)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
#ifndef BTOR_USE_LINGELING
  BTOR_ABORT_BOOLECTOR (1, "cloning requires lingeling as SAT solver");
#endif
  BTOR_TRAPI ("chkclone");
#ifndef NDEBUG
  if (btor->clone) btor_delete_btor (btor->clone);
  btor->clone = btor; /* mark clone as going-to-be shadow clone */
  btor->clone = btor_clone_btor (btor);
  assert (btor->clone->mm);
  assert (btor->clone->avmgr);
  BTOR_CHKCLONE ();
#endif
}

/*------------------------------------------------------------------------*/

Btor *
boolector_new (void)
{
  char *trname;
  Btor *btor;

  btor = btor_new_btor ();
  if ((trname = getenv ("BTORAPITRACE"))) btor_open_apitrace (btor, trname);
  BTOR_TRAPI ("new");
  return btor;
}

Btor *
boolector_clone (Btor *btor)
{
  BTOR_TRAPI ("clone"); /* just log, do nothing else */
  return btor_clone_btor (btor);
}

Btor *
boolector_btor (BoolectorNode *node)
{
  BtorNode *exp, *real_exp, *simp, *real_simp;
  Btor *btor;
  BTOR_ABORT_ARG_NULL_BOOLECTOR (node);
  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  real_exp  = BTOR_REAL_ADDR_NODE (exp);
  simp      = btor_simplify_exp (real_exp->btor, exp);
  real_simp = BTOR_REAL_ADDR_NODE (simp);
  btor      = real_simp->btor;
  assert (real_simp->btor == real_exp->btor);
  BTOR_TRAPI ("btor", exp);
#ifndef NDEBUG
  if (btor->clone)
  {
    Btor *clone = boolector_btor (BTOR_CLONED_EXP (exp));
    assert (clone == btor->clone);
    BTOR_CHKCLONE ();
  }
#endif
  BTOR_TRAPI_RETURN_PTR (btor);
  return btor;
}

void
boolector_set_rewrite_level (Btor *btor, int rewrite_level)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("set_rewrite_level %d", rewrite_level);
  BTOR_ABORT_BOOLECTOR (rewrite_level < 0 || rewrite_level > 3,
                        "'rewrite_level' has to be in [0,3]");
  BTOR_ABORT_BOOLECTOR (
      BTOR_COUNT_STACK (btor->nodes_id_table) > 2,
      "setting rewrite level must be done before creating expressions");
  btor_set_rewrite_level_btor (btor, rewrite_level);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (set_rewrite_level, rewrite_level);
#endif
}

void
boolector_enable_model_gen (Btor *btor)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("enable_model_gen");
  BTOR_ABORT_BOOLECTOR (
      BTOR_COUNT_STACK (btor->nodes_id_table) > 2,
      "enabling model generation must be done before creating expressions");
  btor_enable_model_gen (btor);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (enable_model_gen);
#endif
}

void
boolector_disable_model_gen (Btor *btor)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("disable_model_gen");
  btor_disable_model_gen (btor);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (disable_model_gen);
#endif
}

void
boolector_generate_model_for_all_reads (Btor *btor)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("generate_model_for_all_reads");
  btor_generate_model_for_all_reads (btor);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (generate_model_for_all_reads);
#endif
}

void
boolector_enable_inc_usage (Btor *btor)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("enable_inc_usage");
  BTOR_ABORT_BOOLECTOR (
      btor->btor_sat_btor_called > 0,
      "enabling incremental usage must be done before calling 'boolector_sat'");
  btor_enable_inc_usage (btor);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (enable_inc_usage);
#endif
}

void
boolector_enable_beta_reduce_all (Btor *btor)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("enable_beta_reduce_all");
  btor_enable_beta_reduce_all (btor);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (enable_beta_reduce_all);
#endif
}

void
boolector_enable_dual_prop (Btor *btor)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("enable_dual_prop");
  BTOR_ABORT_BOOLECTOR (
      btor->options.just,
      "enabling multiple optimization techniques is not allowed");
  btor_enable_dual_prop (btor);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (enable_dual_prop);
#endif
}

void
boolector_enable_justification (Btor *btor)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("enable_just");
  BTOR_ABORT_BOOLECTOR (
      btor->options.dual_prop,
      "enabling multiple optimization techniques is not allowed");
  btor_enable_just (btor);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (enable_justification);
#endif
}
void
boolector_enable_force_cleanup (Btor *btor)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("enable_force_cleanup");
  btor_enable_force_cleanup (btor);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (enable_force_cleanup);
#endif
}

#ifndef BTOR_DO_NOT_OPTIMIZE_UNCONSTRAINED
void
boolector_enable_ucopt (Btor *btor)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("enable_ucopt");
  btor_enable_ucopt (btor);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (enable_ucopt);
#endif
}
#else
void
boolector_enable_ucopt (Btor *btor)
{
  (void) btor;
}
#endif

void
boolector_set_verbosity (Btor *btor, int verbosity)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("set_verbosity %d", verbosity);
  btor_set_verbosity_btor (btor, verbosity);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (set_verbosity, verbosity);
#endif
}

void
boolector_set_loglevel (Btor *btor, int loglevel)
{
#ifndef NBTORLOG
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("set_loglevel %d", loglevel);
  btor_set_loglevel_btor (btor, loglevel);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (set_loglevel, loglevel);
#endif
#else
  (void) btor;
  (void) loglevel;
#endif
}

int
boolector_set_sat_solver (Btor *btor, const char *solver)
{
  int res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("set_sat_solver %d", solver);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (solver);
  BTOR_ABORT_BOOLECTOR (
      btor->btor_sat_btor_called > 0,
      "setting the SAT solver must be done before calling 'boolector_sat'");
  res = btor_set_sat_solver (btor, solver);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES (res, set_sat_solver, solver);
#endif
  BTOR_TRAPI_RETURN (res);
  return res;
}

void
boolector_reset_time (Btor *btor)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("reset_time");
  btor_reset_time_btor (btor);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (reset_time);
#endif
}

void
boolector_reset_stats (Btor *btor)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("reset_stats");
  btor_reset_stats_btor (btor);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (reset_stats);
#endif
}

int
boolector_get_refs (Btor *btor)
{
  int res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("get_refs");
  res = btor->external_refs;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES (res, get_refs);
#endif
  BTOR_TRAPI_RETURN (res);
  return res;
}

void
boolector_delete (Btor *btor)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("delete");
  if (btor->closeapitrace == 1)
    fclose (btor->apitrace);
  else if (btor->closeapitrace == 2)
    pclose (btor->apitrace);
  if (btor->clone) boolector_delete (btor->clone);
  btor_delete_btor (btor);
}

int
boolector_simplify (Btor *btor)
{
  int res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("simplify");

  res = btor_simplify (btor);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES (res, simplify);
#endif
  BTOR_TRAPI_RETURN (res);
  return res;
}

BoolectorNode *
boolector_const (Btor *btor, const char *bits)
{
  BtorNode *res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("const %s", bits);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (bits);
  BTOR_ABORT_BOOLECTOR (*bits == '\0', "'bits' must not be empty");
  btor->external_refs++;
  res = btor_const_exp (btor, bits);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, const, bits);
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

int
boolector_is_const (Btor *btor, BoolectorNode *node)
{
  BtorNode *exp, *simp, *real;
  int res;
  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  BTOR_TRAPI ("is_const", exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  simp = btor_simplify_exp (btor, exp);
  real = BTOR_REAL_ADDR_NODE (simp);
  res  = BTOR_IS_BV_CONST_NODE (real);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES (res, is_const, BTOR_CLONED_EXP (exp));
#endif
  BTOR_TRAPI_RETURN (res);
  return res;
}

const char *
boolector_get_bits (Btor *btor, BoolectorNode *node)
{
  BtorNode *exp, *simp, *real;
  const char *res;
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (node);
  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  simp = btor_simplify_exp (btor, exp);
  real = BTOR_REAL_ADDR_NODE (simp);
  BTOR_ABORT_BOOLECTOR (!BTOR_IS_BV_CONST_NODE (real),
                        "argument is not a constant node");
  if (BTOR_IS_INVERTED_NODE (simp))
  {
    if (!real->invbits)
      real->invbits = btor_not_const_3vl (btor->mm, real->bits);
    res = real->invbits;
  }
  else
    res = simp->bits;
#ifndef NDEBUG
  if (btor->clone)
  {
    const char *cloned_res =
        boolector_get_bits (btor->clone, BTOR_CLONED_EXP (node));
    assert (!strcmp (cloned_res, res));
  }
#endif
  return res;
}

BoolectorNode *
boolector_zero (Btor *btor, int width)
{
  BtorNode *res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("zero %d", width);
  BTOR_ABORT_BOOLECTOR (width < 1, "'width' must not be < 1");
  btor->external_refs++;
  res = btor_zero_exp (btor, width);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, zero, width);
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_false (Btor *btor)
{
  BtorNode *res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("false");
  btor->external_refs++;
  res = btor_false_exp (btor);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, false);
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_ones (Btor *btor, int width)
{
  BtorNode *res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("ones %d", width);
  BTOR_ABORT_BOOLECTOR (width < 1, "'width' must not be < 1");
  btor->external_refs++;
  res = btor_ones_exp (btor, width);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, ones, width);
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_true (Btor *btor)
{
  BtorNode *res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("true");
  btor->external_refs++;
  res = btor_true_exp (btor);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, true);
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_one (Btor *btor, int width)
{
  BtorNode *res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("one %d", width);
  BTOR_ABORT_BOOLECTOR (width < 1, "'width' must not be < 1");
  btor->external_refs++;
  res = btor_one_exp (btor, width);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, one, width);
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_unsigned_int (Btor *btor, unsigned int u, int width)
{
  BtorNode *res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("unsigned_int %u %d", u, width);
  BTOR_ABORT_BOOLECTOR (width < 1, "'width' must not be < 1");
  btor->external_refs++;
  res = btor_unsigned_exp (btor, u, width);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, unsigned_int, u, width);
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_int (Btor *btor, int i, int width)
{
  BtorNode *res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("int %d %u", i, width);
  BTOR_ABORT_BOOLECTOR (width < 1, "'width' must not be < 1");
  btor->external_refs++;
  res = btor_int_exp (btor, i, width);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, int, i, width);
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_var (Btor *btor, int width, const char *symbol)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);

  BtorNode *res;
  char *symb;

  if ((symb = (char *) symbol) == NULL)
  {
    BTOR_NEWN (btor->mm, symb, 20);
    sprintf (symb, "DVN%d", btor->dvn_id++);
    BTOR_TRAPI ("var %d %s", width, symb);
    BTOR_ABORT_BOOLECTOR (width < 1, "'width' must not be < 1");
    btor->external_refs++;
    res = btor_var_exp (btor, width, symb);
  }
  else
  {
    BTOR_TRAPI ("var %d %s", width, symbol);
    BTOR_ABORT_BOOLECTOR (width < 1, "'width' must not be < 1");
    btor->external_refs++;
    res = btor_var_exp (btor, width, symbol);
  }

  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;

  if (symbol == NULL) BTOR_DELETEN (btor->mm, symb, 20);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, var, width, symbol);
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

int
boolector_is_var (Btor *btor, BoolectorNode *node)
{
  BtorNode *exp, *simp, *real;
  int res;
  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_TRAPI ("is_var", exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  simp = btor_simplify_exp (btor, exp);
  real = BTOR_REAL_ADDR_NODE (simp);
  res  = BTOR_IS_BV_VAR_NODE (real);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES (res, is_const, BTOR_CLONED_EXP (exp));
#endif
  BTOR_TRAPI_RETURN (res);
  return res;
}

BoolectorNode *
boolector_array (Btor *btor,
                 int elem_width,
                 int index_width,
                 const char *symbol)
{
  BtorNode *res;
  char *symb;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);

  if ((symb = (char *) symbol) == NULL)
  {
    BTOR_NEWN (btor->mm, symb, 20);
    sprintf (symb, "DAN%d", btor->dan_id++);
    BTOR_TRAPI ("array %d %d %s", elem_width, index_width, symb);
    BTOR_ABORT_BOOLECTOR (elem_width < 1, "'elem_width' must not be < 1");
    BTOR_ABORT_BOOLECTOR (index_width < 1, "'index_width' must not be < 1");
    btor->external_refs++;
    res = btor_array_exp (btor, elem_width, index_width, symb);
  }
  else
  {
    BTOR_TRAPI ("array %d %d %s", elem_width, index_width, symbol);
    BTOR_ABORT_BOOLECTOR (elem_width < 1, "'elem_width' must not be < 1");
    BTOR_ABORT_BOOLECTOR (index_width < 1, "'index_width' must not be < 1");
    btor->external_refs++;
    res = btor_array_exp (btor, elem_width, index_width, symbol);
  }
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
  if (symbol == NULL) BTOR_DELETEN (btor->mm, symb, 20);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, array, elem_width, index_width, symbol);
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_not (Btor *btor, BoolectorNode *node)
{
  BtorNode *exp, *simp, *res;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_TRAPI_UNFUN ("not", exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  simp = btor_simplify_exp (btor, exp);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp);
  btor->external_refs++;
  res = btor_not_exp (btor, simp);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, not, BTOR_CLONED_EXP (exp));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_neg (Btor *btor, BoolectorNode *node)
{
  BtorNode *exp, *simp, *res;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_TRAPI_UNFUN ("neg", exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  simp = btor_simplify_exp (btor, exp);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp);
  btor->external_refs++;
  res = btor_neg_exp (btor, simp);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, neg, BTOR_CLONED_EXP (exp));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_redor (Btor *btor, BoolectorNode *node)
{
  BtorNode *exp, *simp, *res;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_TRAPI_UNFUN ("redor", exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  simp = btor_simplify_exp (btor, exp);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp);
  btor->external_refs++;
  res = btor_redor_exp (btor, simp);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, redor, BTOR_CLONED_EXP (exp));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_redxor (Btor *btor, BoolectorNode *node)
{
  BtorNode *exp, *simp, *res;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_TRAPI_UNFUN ("redxor", exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  simp = btor_simplify_exp (btor, exp);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp);
  btor->external_refs++;
  res = btor_redxor_exp (btor, simp);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, redxor, BTOR_CLONED_EXP (exp));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_redand (Btor *btor, BoolectorNode *node)
{
  BtorNode *exp, *simp, *res;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_TRAPI_UNFUN ("redand", exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  simp = btor_simplify_exp (btor, exp);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp);
  btor->external_refs++;
  res = btor_redand_exp (btor, simp);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, redand, BTOR_CLONED_EXP (exp));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_slice (Btor *btor, BoolectorNode *node, int upper, int lower)
{
  BtorNode *exp, *simp, *res;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_TRAPI_UNFUN_EXT ("slice", exp, "%d %d", upper, lower);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  simp = btor_simplify_exp (btor, exp);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp);
  BTOR_ABORT_BOOLECTOR (lower < 0, "'lower' must not be negative");
  BTOR_ABORT_BOOLECTOR (upper < lower, "'upper' must not be < 'lower'");
  BTOR_ABORT_BOOLECTOR (upper >= BTOR_REAL_ADDR_NODE (simp)->len,
                        "'upper' must not be >= width of 'exp'");
  btor->external_refs++;
  res = btor_slice_exp (btor, simp, upper, lower);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, slice, BTOR_CLONED_EXP (exp), upper, lower);
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_uext (Btor *btor, BoolectorNode *node, int width)
{
  BtorNode *exp, *simp, *res;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_TRAPI_UNFUN_EXT ("uext", exp, "%d", width);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  simp = btor_simplify_exp (btor, exp);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp);
  BTOR_ABORT_BOOLECTOR (width < 0, "'width' must not be negative");
  btor->external_refs++;
  res = btor_uext_exp (btor, simp, width);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, uext, BTOR_CLONED_EXP (exp), width);
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_sext (Btor *btor, BoolectorNode *node, int width)
{
  BtorNode *exp, *simp, *res;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_TRAPI_UNFUN_EXT ("sext", exp, "%d", width);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  simp = btor_simplify_exp (btor, exp);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp);
  BTOR_ABORT_BOOLECTOR (width < 0, "'width' must not be negative");
  btor->external_refs++;
  res = btor_sext_exp (btor, simp, width);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, sext, BTOR_CLONED_EXP (exp), width);
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_implies (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *simp0, *simp1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_TRAPI_BINFUN ("implies", e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_BOOLECTOR (BTOR_REAL_ADDR_NODE (simp0)->len != 1
                            || BTOR_REAL_ADDR_NODE (simp1)->len != 1,
                        "bit-width of 'e0' and 'e1' have be 1");
  btor->external_refs++;
  res = btor_implies_exp (btor, simp0, simp1);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (
      res, implies, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_iff (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *simp0, *simp1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_TRAPI_BINFUN ("iff", e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_BOOLECTOR (BTOR_REAL_ADDR_NODE (simp0)->len != 1
                            || BTOR_REAL_ADDR_NODE (simp1)->len != 1,
                        "bit-width of 'e0' and 'e1' must not be unequal to 1");
  btor->external_refs++;
  res = btor_iff_exp (btor, simp0, simp1);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, iff, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_xor (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *simp0, *simp1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_TRAPI_BINFUN ("xor", e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  btor->external_refs++;
  res = btor_xor_exp (btor, simp0, simp1);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, xor, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_xnor (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *simp0, *simp1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_TRAPI_BINFUN ("xnor", e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  btor->external_refs++;
  res = btor_xnor_exp (btor, simp0, simp1);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, xnor, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_and (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *simp0, *simp1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_TRAPI_BINFUN ("and", e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  btor->external_refs++;
  res = btor_and_exp (btor, simp0, simp1);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, and, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_nand (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *simp0, *simp1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_TRAPI_BINFUN ("nand", e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  btor->external_refs++;
  res = btor_nand_exp (btor, simp0, simp1);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, nand, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_or (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *simp0, *simp1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_TRAPI_BINFUN ("or", e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  btor->external_refs++;
  res = btor_or_exp (btor, simp0, simp1);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, or, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_nor (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *simp0, *simp1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_TRAPI_BINFUN ("nor", e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  btor->external_refs++;
  res = btor_nor_exp (btor, simp0, simp1);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, nor, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_eq (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *simp0, *simp1, *real_simp0, *real_simp1, *res;
  int is_array_simp0, is_array_simp1;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_TRAPI_BINFUN ("eq", e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0          = btor_simplify_exp (btor, e0);
  simp1          = btor_simplify_exp (btor, e1);
  real_simp0     = BTOR_REAL_ADDR_NODE (simp0);
  real_simp1     = BTOR_REAL_ADDR_NODE (simp1);
  is_array_simp0 = BTOR_IS_FUN_NODE (real_simp0);
  is_array_simp1 = BTOR_IS_FUN_NODE (real_simp1);
  BTOR_ABORT_BOOLECTOR (
      BTOR_IS_UF_NODE (real_simp0) || BTOR_IS_UF_NODE (real_simp1),
      "equality of UF not supported yet");
  BTOR_ABORT_BOOLECTOR (is_array_simp0 != is_array_simp1,
                        "array must not be compared to bit-vector");
  BTOR_ABORT_BOOLECTOR (!is_array_simp0 && real_simp0 && real_simp1
                            && real_simp0->len != real_simp1->len,
                        "bit-vectors must not have unequal bit-width");
  BTOR_ABORT_BOOLECTOR (is_array_simp0 && real_simp0 && real_simp1
                            && real_simp0->len != real_simp1->len,
                        "arrays must not have unequal element bit-width");
  BTOR_ABORT_BOOLECTOR (is_array_simp0 && real_simp0 && real_simp1
                            && BTOR_ARRAY_INDEX_LEN (real_simp0)
                                   != BTOR_ARRAY_INDEX_LEN (real_simp1),
                        "arrays must not have unequal index bit-width");
  btor->external_refs++;
  res = btor_eq_exp (btor, simp0, simp1);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, eq, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_ne (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *simp0, *simp1, *real_simp0, *real_simp1, *res;
  int is_array_simp0, is_array_simp1;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_TRAPI_BINFUN ("ne", e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0          = btor_simplify_exp (btor, e0);
  simp1          = btor_simplify_exp (btor, e1);
  real_simp0     = BTOR_REAL_ADDR_NODE (simp0);
  real_simp1     = BTOR_REAL_ADDR_NODE (simp1);
  is_array_simp0 = BTOR_IS_FUN_NODE (real_simp0);
  is_array_simp1 = BTOR_IS_FUN_NODE (real_simp1);
  BTOR_ABORT_BOOLECTOR (is_array_simp0 != is_array_simp1,
                        "array must not be compared to bit-vector");
  BTOR_ABORT_BOOLECTOR (is_array_simp0 && real_simp0->len != real_simp1->len,
                        "arrays must not have unequal element bit-width");
  BTOR_ABORT_BOOLECTOR (is_array_simp0
                            && BTOR_ARRAY_INDEX_LEN (real_simp0)
                                   != BTOR_ARRAY_INDEX_LEN (real_simp1),
                        "arrays must not have unequal index bit-width");
  btor->external_refs++;
  res = btor_ne_exp (btor, simp0, simp1);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, ne, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_add (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *simp0, *simp1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_TRAPI_BINFUN ("add", e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  btor->external_refs++;
  res = btor_add_exp (btor, simp0, simp1);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, add, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_uaddo (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *simp0, *simp1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_TRAPI_BINFUN ("uaddo", e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  btor->external_refs++;
  res = btor_uaddo_exp (btor, simp0, simp1);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (
      res, uaddo, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_saddo (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *simp0, *simp1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_TRAPI_BINFUN ("saddo", e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  btor->external_refs++;
  res = btor_saddo_exp (btor, simp0, simp1);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (
      res, saddo, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_mul (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *simp0, *simp1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_TRAPI_BINFUN ("mul", e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  btor->external_refs++;
  res = btor_mul_exp (btor, simp0, simp1);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, mul, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_umulo (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *simp0, *simp1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_TRAPI_BINFUN ("umulo", e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  btor->external_refs++;
  res = btor_umulo_exp (btor, simp0, simp1);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (
      res, umulo, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_smulo (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *simp0, *simp1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_TRAPI_BINFUN ("smulo", e0, e1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  btor->external_refs++;
  res = btor_smulo_exp (btor, simp0, simp1);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (
      res, smulo, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_ult (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *simp0, *simp1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_TRAPI_BINFUN ("ult", e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  btor->external_refs++;
  res = btor_ult_exp (btor, simp0, simp1);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, ult, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_slt (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *simp0, *simp1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_TRAPI_BINFUN ("slt", e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  btor->external_refs++;
  res = btor_slt_exp (btor, simp0, simp1);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, slt, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_ulte (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *simp0, *simp1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_TRAPI_BINFUN ("ulte", e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  btor->external_refs++;
  res = btor_ulte_exp (btor, simp0, simp1);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, ulte, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_slte (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *simp0, *simp1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_TRAPI_BINFUN ("slte", e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  btor->external_refs++;
  res = btor_slte_exp (btor, simp0, simp1);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, slte, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_ugt (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *simp0, *simp1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_TRAPI_BINFUN ("ugt", e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  btor->external_refs++;
  res = btor_ugt_exp (btor, simp0, simp1);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, ugt, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_sgt (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *simp0, *simp1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_TRAPI_BINFUN ("sgt", e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  btor->external_refs++;
  res = btor_sgt_exp (btor, simp0, simp1);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, sgt, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_ugte (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *simp0, *simp1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_TRAPI_BINFUN ("ugte", e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  btor->external_refs++;
  res = btor_ugte_exp (btor, simp0, simp1);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, ugte, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_sgte (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *simp0, *simp1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_TRAPI_BINFUN ("sgte", e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  btor->external_refs++;
  res = btor_sgte_exp (btor, simp0, simp1);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, sgte, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_sll (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  int len;
  BtorNode *e0, *e1, *simp0, *simp1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_TRAPI_BINFUN ("sll", e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  len = BTOR_REAL_ADDR_NODE (simp0)->len;
  BTOR_ABORT_BOOLECTOR (!btor_is_power_of_2_util (len),
                        "bit-width of 'e0' must be a power of 2");
  BTOR_ABORT_BOOLECTOR (
      btor_log_2_util (len) != BTOR_REAL_ADDR_NODE (simp1)->len,
      "bit-width of 'e1' must be equal to log2(bit-width of 'e0')");
  btor->external_refs++;
  res = btor_sll_exp (btor, simp0, simp1);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, sll, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_srl (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  int len;
  BtorNode *e0, *e1, *simp0, *simp1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_TRAPI_BINFUN ("srl", e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  len = BTOR_REAL_ADDR_NODE (simp0)->len;
  BTOR_ABORT_BOOLECTOR (!btor_is_power_of_2_util (len),
                        "bit-width of 'e0' must be a power of 2");
  BTOR_ABORT_BOOLECTOR (
      btor_log_2_util (len) != BTOR_REAL_ADDR_NODE (simp1)->len,
      "bit-width of 'e1' must be equal to log2(bit-width of 'e0')");
  btor->external_refs++;
  res = btor_srl_exp (btor, simp0, simp1);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, srl, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_sra (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  int len;
  BtorNode *e0, *e1, *simp0, *simp1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_TRAPI_BINFUN ("sra", e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  len = BTOR_REAL_ADDR_NODE (simp0)->len;
  BTOR_ABORT_BOOLECTOR (!btor_is_power_of_2_util (len),
                        "bit-width of 'e0' must be a power of 2");
  BTOR_ABORT_BOOLECTOR (
      btor_log_2_util (len) != BTOR_REAL_ADDR_NODE (simp1)->len,
      "bit-width of 'e1' must be equal to log2(bit-width of 'e0')");
  btor->external_refs++;
  res = btor_sra_exp (btor, simp0, simp1);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, sra, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_rol (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  int len;
  BtorNode *e0, *e1, *simp0, *simp1, *res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_TRAPI_BINFUN ("rol", e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  len = BTOR_REAL_ADDR_NODE (simp0)->len;
  BTOR_ABORT_BOOLECTOR (!btor_is_power_of_2_util (len),
                        "bit-width of 'e0' must be a power of 2");
  BTOR_ABORT_BOOLECTOR (
      btor_log_2_util (len) != BTOR_REAL_ADDR_NODE (simp1)->len,
      "bit-width of 'e1' must be equal to log2(bit-width of 'e0')");
  btor->external_refs++;
  res = btor_rol_exp (btor, simp0, simp1);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, rol, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_ror (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  int len;
  BtorNode *e0, *e1, *simp0, *simp1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_TRAPI_BINFUN ("ror", e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  len = BTOR_REAL_ADDR_NODE (simp0)->len;
  BTOR_ABORT_BOOLECTOR (!btor_is_power_of_2_util (len),
                        "bit-width of 'e0' must be a power of 2");
  BTOR_ABORT_BOOLECTOR (
      btor_log_2_util (len) != BTOR_REAL_ADDR_NODE (simp1)->len,
      "bit-width of 'e1' must be equal to log2(bit-width of 'e0')");
  btor->external_refs++;
  res = btor_ror_exp (btor, simp0, simp1);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, ror, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_sub (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *simp0, *simp1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_TRAPI_BINFUN ("sub", e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  btor->external_refs++;
  res = btor_sub_exp (btor, simp0, simp1);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, sub, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_usubo (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *simp0, *simp1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_TRAPI_BINFUN ("usubo", e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  btor->external_refs++;
  res = btor_usubo_exp (btor, simp0, simp1);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (
      res, usubo, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_ssubo (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *simp0, *simp1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_TRAPI_BINFUN ("ssubo", e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  btor->external_refs++;
  res = btor_ssubo_exp (btor, simp0, simp1);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (
      res, ssubo, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_udiv (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *simp0, *simp1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_TRAPI_BINFUN ("udiv", e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  btor->external_refs++;
  res = btor_udiv_exp (btor, simp0, simp1);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, udiv, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_sdiv (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *simp0, *simp1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_TRAPI_BINFUN ("sdiv", e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  btor->external_refs++;
  res = btor_sdiv_exp (btor, simp0, simp1);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, sdiv, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_sdivo (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *simp0, *simp1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_TRAPI_BINFUN ("sdivo", e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  btor->external_refs++;
  res = btor_sdivo_exp (btor, simp0, simp1);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (
      res, sdivo, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_urem (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *simp0, *simp1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_TRAPI_BINFUN ("urem", e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  btor->external_refs++;
  res = btor_urem_exp (btor, simp0, simp1);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, urem, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_srem (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *simp0, *simp1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_TRAPI_BINFUN ("srem", e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  btor->external_refs++;
  res = btor_srem_exp (btor, simp0, simp1);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, srem, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_smod (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *simp0, *simp1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_TRAPI_BINFUN ("smod", e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_NE_BW (simp0, simp1);
  btor->external_refs++;
  res = btor_smod_exp (btor, simp0, simp1);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, smod, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_concat (Btor *btor, BoolectorNode *n0, BoolectorNode *n1)
{
  BtorNode *e0, *e1, *simp0, *simp1, *res;

  e0 = BTOR_IMPORT_BOOLECTOR_NODE (n0);
  e1 = BTOR_IMPORT_BOOLECTOR_NODE (n1);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e0);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e1);
  BTOR_TRAPI_BINFUN ("concat", e0, e1);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e0);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e1);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e0);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e1);
  simp0 = btor_simplify_exp (btor, e0);
  simp1 = btor_simplify_exp (btor, e1);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp0);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp1);
  BTOR_ABORT_BOOLECTOR (BTOR_REAL_ADDR_NODE (e0)->len
                            > INT_MAX - BTOR_REAL_ADDR_NODE (simp1)->len,
                        "bit-width of result is too large");
  btor->external_refs++;
  res = btor_concat_exp (btor, simp0, simp1);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (
      res, concat, BTOR_CLONED_EXP (e0), BTOR_CLONED_EXP (e1));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_read (Btor *btor, BoolectorNode *n_array, BoolectorNode *n_index)
{
  BtorNode *e_array, *e_index, *simp_array, *simp_index, *res;

  e_array = BTOR_IMPORT_BOOLECTOR_NODE (n_array);
  e_index = BTOR_IMPORT_BOOLECTOR_NODE (n_index);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e_array);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e_index);
  BTOR_TRAPI_BINFUN ("read", e_array, e_index);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e_array);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e_index);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e_array);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e_index);
  simp_array = btor_simplify_exp (btor, e_array);
  simp_index = btor_simplify_exp (btor, e_index);
  BTOR_ABORT_BV_BOOLECTOR (simp_array);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp_index);
  BTOR_ABORT_BOOLECTOR (
      BTOR_ARRAY_INDEX_LEN (simp_array)
          != BTOR_REAL_ADDR_NODE (simp_index)->len,
      "index bit-width of 'e_array' and bit-width of 'e_index' must be equal");
  btor->external_refs++;
  res = btor_read_exp (btor, simp_array, simp_index);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (
      res, read, BTOR_CLONED_EXP (e_array), BTOR_CLONED_EXP (e_index));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_write (Btor *btor,
                 BoolectorNode *n_array,
                 BoolectorNode *n_index,
                 BoolectorNode *n_value)
{
  BtorNode *e_array, *e_index, *e_value, *simp_array, *simp_index, *simp_value;
  BtorNode *res;

  e_array = BTOR_IMPORT_BOOLECTOR_NODE (n_array);
  e_index = BTOR_IMPORT_BOOLECTOR_NODE (n_index);
  e_value = BTOR_IMPORT_BOOLECTOR_NODE (n_value);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e_array);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e_index);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e_value);
  BTOR_TRAPI_TERFUN ("write", e_array, e_index, e_value);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e_array);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e_index);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e_value);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e_array);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e_index);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e_value);
  simp_array = btor_simplify_exp (btor, e_array);
  simp_index = btor_simplify_exp (btor, e_index);
  simp_value = btor_simplify_exp (btor, e_value);
  BTOR_ABORT_BV_BOOLECTOR (simp_array);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp_index);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp_value);
  BTOR_ABORT_BOOLECTOR (
      BTOR_ARRAY_INDEX_LEN (simp_array)
          != BTOR_REAL_ADDR_NODE (simp_index)->len,
      "index bit-width of 'e_array' and bit-width of 'e_index' must be equal");
  BTOR_ABORT_BOOLECTOR (
      simp_array->len != BTOR_REAL_ADDR_NODE (simp_value)->len,
      "element bit-width of 'e_array' and bit-width of 'e_value' must be "
      "equal");
  btor->external_refs++;
  res = btor_write_exp (btor, simp_array, simp_index, simp_value);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res,
                         write,
                         BTOR_CLONED_EXP (e_array),
                         BTOR_CLONED_EXP (e_index),
                         BTOR_CLONED_EXP (e_value));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_cond (Btor *btor,
                BoolectorNode *n_cond,
                BoolectorNode *n_if,
                BoolectorNode *n_else)
{
  BtorNode *e_cond, *e_if, *e_else;
  BtorNode *simp_cond, *simp_if, *simp_else, *real_simp_if, *real_simp_else;
  BtorNode *res;
  int is_array_simp_if, is_array_simp_else;

  e_cond = BTOR_IMPORT_BOOLECTOR_NODE (n_cond);
  e_if   = BTOR_IMPORT_BOOLECTOR_NODE (n_if);
  e_else = BTOR_IMPORT_BOOLECTOR_NODE (n_else);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e_cond);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e_if);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e_else);
  BTOR_TRAPI_TERFUN ("cond", e_cond, e_if, e_else);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e_cond);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e_if);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e_else);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e_cond);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e_if);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e_else);
  simp_cond = btor_simplify_exp (btor, e_cond);
  simp_if   = btor_simplify_exp (btor, e_if);
  simp_else = btor_simplify_exp (btor, e_else);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp_cond);
  BTOR_ABORT_BOOLECTOR (BTOR_REAL_ADDR_NODE (simp_cond)->len != 1,
                        "bit-width of 'e_cond' must be equal to 1");
  real_simp_if       = BTOR_REAL_ADDR_NODE (simp_if);
  real_simp_else     = BTOR_REAL_ADDR_NODE (simp_else);
  is_array_simp_if   = BTOR_IS_FUN_NODE (real_simp_if);
  is_array_simp_else = BTOR_IS_FUN_NODE (real_simp_else);
  BTOR_ABORT_BOOLECTOR (is_array_simp_if != is_array_simp_else,
                        "array must not be combined with bit-vector");
  BTOR_ABORT_BOOLECTOR (!is_array_simp_if && real_simp_if && real_simp_else
                            && real_simp_if->len != real_simp_else->len,
                        "bit-vectors must not have unequal bit-width");
  BTOR_ABORT_BOOLECTOR (is_array_simp_if && real_simp_if && real_simp_else
                            && real_simp_if->len != real_simp_else->len,
                        "arrays must not have unequal element bit-width");
  BTOR_ABORT_BOOLECTOR (is_array_simp_if && real_simp_if && real_simp_else
                            && BTOR_ARRAY_INDEX_LEN (real_simp_if)
                                   != BTOR_ARRAY_INDEX_LEN (real_simp_else),
                        "arrays must not have unequal index bit-width");
  btor->external_refs++;
  res = btor_cond_exp (btor, simp_cond, simp_if, simp_else);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res,
                         cond,
                         BTOR_CLONED_EXP (e_cond),
                         BTOR_CLONED_EXP (e_if),
                         BTOR_CLONED_EXP (e_else));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_param (Btor *btor, int width, const char *symbol)
{
  BtorNode *res;
  char *symb;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);

  if ((symb = (char *) symbol) == NULL)
  {
    BTOR_NEWN (btor->mm, symb, 20);
    sprintf (symb, "DPN%d", btor->dpn_id++);
    BTOR_TRAPI ("param %d %s", width, symb);
    BTOR_ABORT_BOOLECTOR (width < 1, "'width' must not be < 1");
    btor->external_refs++;
    res = btor_param_exp (btor, width, symb);
  }
  else
  {
    BTOR_TRAPI ("param %d %s", width, symbol);
    BTOR_ABORT_BOOLECTOR (width < 1, "'width' must not be < 1");
    btor->external_refs++;
    res = btor_param_exp (btor, width, symbol);
  }
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;

  if (symbol == NULL) BTOR_DELETEN (btor->mm, symb, 20);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, param, width, symbol);
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_fun (Btor *btor,
               int paramc,
               BoolectorNode **param_nodes,
               BoolectorNode *node)
{
  int i, len;
  char *strtrapi;
  BtorNode **params, *exp, *res;

  params = BTOR_IMPORT_BOOLECTOR_NODE_ARRAY (param_nodes);
  exp    = BTOR_IMPORT_BOOLECTOR_NODE (node);

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (params);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  BTOR_ABORT_BOOLECTOR (paramc < 1, "'paramc' must not be < 1");

  len = 5 + 10 + paramc * 20 + 20;
  BTOR_NEWN (btor->mm, strtrapi, len);
  sprintf (strtrapi, "fun %d", paramc);

  for (i = 0; i < paramc; i++)
  {
    BTOR_ABORT_BOOLECTOR (
        !params[i] || !BTOR_IS_PARAM_NODE (BTOR_REAL_ADDR_NODE (params[i])),
        "'params[%d]' is not a parameter",
        i);
    BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (params[i]);
    sprintf (
        strtrapi + strlen (strtrapi), NODE_FMT, BTOR_TRAPI_NODE_ID (params[i]));
  }
  sprintf (strtrapi + strlen (strtrapi), NODE_FMT, BTOR_TRAPI_NODE_ID (exp));
  BTOR_TRAPI (strtrapi);
  BTOR_DELETEN (btor->mm, strtrapi, len);
  btor->external_refs++;
  res = btor_fun_exp (btor, paramc, params, exp);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BoolectorNode *cparam_nodes[paramc];
  for (i = 0; btor->clone && i < paramc; i++)
    cparam_nodes[i] = BTOR_CLONED_EXP (params[i]);
  BTOR_CHKCLONE_RES_PTR (res, fun, paramc, cparam_nodes, BTOR_CLONED_EXP (exp));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_uf (Btor *btor, BoolectorSort *sort, const char *symbol)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (sort);
  BTOR_ABORT_BOOLECTOR (((BtorSort *) sort)->kind != BTOR_FUN_SORT,
                        "given UF sort is not BTOR_FUN_SORT");
  BtorNode *res;

  res = btor_uf_exp (btor, (BtorSort *) sort, symbol);
  res->ext_refs++;
  btor->external_refs++;
  return (BoolectorNode *) res;
}

BoolectorSort *
boolector_bitvec_sort (Btor *btor, int len)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_BOOLECTOR (len <= 0, "'len' must be > 0");

  BtorSort *res;
  res = btor_bitvec_sort (&btor->sorts_unique_table, len);
  res->ext_refs++;
  return (BoolectorSort *) res;
}

BoolectorSort *
boolector_tuple_sort (Btor *btor, BoolectorSort **elements, int num_elements)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (elements);
  BTOR_ABORT_BOOLECTOR (num_elements <= 1, "'num_elements' must be > 1");

  BtorSort *res;
  res = btor_tuple_sort (
      &btor->sorts_unique_table, (BtorSort **) elements, num_elements);
  res->ext_refs++;
  return (BoolectorSort *) res;
}

BoolectorSort *
boolector_fun_sort (Btor *btor, BoolectorSort *domain, BoolectorSort *codomain)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (domain);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (codomain);

  BtorSort *res;

  res = btor_fun_sort (
      &btor->sorts_unique_table, (BtorSort *) domain, (BtorSort *) codomain);
  res->ext_refs++;
  return (BoolectorSort *) res;
}

void
boolector_release_sort (Btor *btor, BoolectorSort *sort)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (sort);

  BtorSort *s = (BtorSort *) sort;
  assert (s->ext_refs > 0);
  s->ext_refs--;
  btor_release_sort (&btor->sorts_unique_table, (BtorSort *) sort);
}

BoolectorNode *
boolector_args (Btor *btor, int argc, BoolectorNode **arg_nodes)
{
  int i, len;
  char *strtrapi;
  BtorNode **args, *res;

  args = BTOR_IMPORT_BOOLECTOR_NODE_ARRAY (arg_nodes);

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (args);
  BTOR_ABORT_BOOLECTOR (argc < 1, "'argc' must not be < 1");

  len = 6 + 10 + argc * 20;
  BTOR_NEWN (btor->mm, strtrapi, len);
  sprintf (strtrapi, "args %d", argc);

  for (i = 0; i < argc; i++)
  {
    BTOR_ABORT_ARG_NULL_BOOLECTOR (args[i]);
    BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (args[i]);
    BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, args[i]);
    sprintf (
        strtrapi + strlen (strtrapi), NODE_FMT, BTOR_TRAPI_NODE_ID (args[i]));
  }
  BTOR_TRAPI (strtrapi);
  BTOR_DELETEN (btor->mm, strtrapi, len);
  btor->external_refs++;
  res = btor_args_exp (btor, argc, args);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BoolectorNode *carg_nodes[argc];
  for (i = 0; btor->clone && i < argc; i++)
    carg_nodes[i] = BTOR_CLONED_EXP (args[i]);
  BTOR_CHKCLONE_RES_PTR (res, args, argc, carg_nodes);
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_apply (Btor *btor,
                 int argc,
                 BoolectorNode **arg_nodes,
                 BoolectorNode *n_fun)
{
  int i, len;
  char *strtrapi;
  BtorNode **args, *e_fun, *res, *cur;

  args  = BTOR_IMPORT_BOOLECTOR_NODE_ARRAY (arg_nodes);
  e_fun = BTOR_IMPORT_BOOLECTOR_NODE (n_fun);

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e_fun);

  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (n_fun);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, n_fun);

  len = 7 + 10 + argc * 20 + 20;
  BTOR_NEWN (btor->mm, strtrapi, len);
  sprintf (strtrapi, "apply %d", argc);

  cur = BTOR_REAL_ADDR_NODE (btor_simplify_exp (btor, e_fun));
  for (i = 0; i < argc; i++)
  {
    BTOR_ABORT_BOOLECTOR (
        !BTOR_IS_UF_NODE (cur) && !BTOR_IS_LAMBDA_NODE (cur),
        "number of arguments must be <= number of parameters in 'fun'");
    sprintf (
        strtrapi + strlen (strtrapi), NODE_FMT, BTOR_TRAPI_NODE_ID (args[i]));
    if (!BTOR_IS_UF_NODE (cur))
      cur = BTOR_REAL_ADDR_NODE (btor_simplify_exp (btor, cur->e[1]));
  }
  sprintf (strtrapi + strlen (strtrapi), NODE_FMT, BTOR_TRAPI_NODE_ID (e_fun));

  BTOR_TRAPI (strtrapi);
  BTOR_DELETEN (btor->mm, strtrapi, len);

  e_fun = btor_simplify_exp (btor, e_fun);
  BTOR_ABORT_BOOLECTOR (argc < 1, "'argc' must not be < 1");
  BTOR_ABORT_BOOLECTOR (argc >= 1 && !args,
                        "no arguments given but argc defined > 0");
  BTOR_ABORT_BOOLECTOR (!btor_is_fun_exp (btor, e_fun)
                            || argc != btor_get_fun_arity (btor, e_fun),
                        "number of arguments does not match arity of 'fun'");
  i = btor_fun_sort_check (btor, argc, args, e_fun);
  BTOR_ABORT_BOOLECTOR (i >= 0,
                        "sort of argument at position %d does not match given"
                        " function signature",
                        i);
  btor->external_refs++;
  res = btor_apply_exps (btor, argc, args, e_fun);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BoolectorNode *carg_nodes[argc];
  for (i = 0; btor->clone && i < argc; i++)
    carg_nodes[i] = BTOR_CLONED_EXP (args[i]);
  BTOR_CHKCLONE_RES_PTR (res, apply, argc, carg_nodes, BTOR_CLONED_EXP (e_fun));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_apply_args (Btor *btor, BoolectorNode *n_args, BoolectorNode *n_fun)
{
  BtorNode *e_args, *e_fun, *res;

  e_args = BTOR_IMPORT_BOOLECTOR_NODE (n_args);
  e_fun  = BTOR_IMPORT_BOOLECTOR_NODE (n_fun);

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e_args);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e_fun);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e_args);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e_fun);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e_args);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e_fun);
  BTOR_TRAPI_BINFUN ("apply_args", e_args, e_fun);
  BTOR_ABORT_BOOLECTOR (!BTOR_IS_REGULAR_NODE (e_args),
                        "'args' must not be inverted");
  BTOR_ABORT_BOOLECTOR (!BTOR_IS_ARGS_NODE (e_args),
                        "'args' is not an argument node");
  btor->external_refs++;
  res = btor_apply_exp (btor, e_fun, e_args);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (
      res, apply_args, BTOR_CLONED_EXP (e_args), BTOR_CLONED_EXP (e_fun));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_inc (Btor *btor, BoolectorNode *node)
{
  BtorNode *exp, *simp, *res;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_TRAPI_UNFUN ("inc", exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  simp = btor_simplify_exp (btor, exp);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp);

  btor->external_refs++;
  res = btor_inc_exp (btor, simp);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, inc, BTOR_CLONED_EXP (exp));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

BoolectorNode *
boolector_dec (Btor *btor, BoolectorNode *node)
{
  BtorNode *exp, *simp, *res;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_TRAPI_UNFUN ("dec", exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  simp = btor_simplify_exp (btor, exp);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp);

  btor->external_refs++;
  res = btor_dec_exp (btor, simp);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, dec, BTOR_CLONED_EXP (exp));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

int
boolector_get_width (Btor *btor, BoolectorNode *node)
{
  int res;
  BtorNode *exp;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_TRAPI_UNFUN ("get_width", exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  res = btor_get_exp_len (btor, exp);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES (res, get_width, BTOR_CLONED_EXP (exp));
#endif
  BTOR_TRAPI_RETURN (res);
  return res;
}

int
boolector_is_array (Btor *btor, BoolectorNode *node)
{
  int res;
  BtorNode *exp, *simp;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_TRAPI_UNFUN ("is_array", exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  simp = btor_simplify_exp (btor, exp);
  res  = btor_is_array_exp (btor, simp);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES (res, is_array, BTOR_CLONED_EXP (exp));
#endif
  BTOR_TRAPI_RETURN (res);
  return res;
}

int
boolector_is_array_var (Btor *btor, BoolectorNode *node)
{
  int res;
  BtorNode *exp, *simp;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_TRAPI_UNFUN ("is_array_var", exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  simp = btor_simplify_exp (btor, exp);
  res  = btor_is_array_var_exp (btor, simp);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES (res, is_array_var, BTOR_CLONED_EXP (exp));
#endif
  BTOR_TRAPI_RETURN (res);
  return res;
}
int
boolector_is_param (Btor *btor, BoolectorNode *node)
{
  BtorNode *exp, *simp;
  int res;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_TRAPI_UNFUN ("is_param", exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  simp = btor_simplify_exp (btor, exp);
  res  = btor_is_param_exp (btor, simp);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES (res, is_param, node);
#endif
  BTOR_TRAPI_RETURN (res);
  return res;
}

int
boolector_is_bound_param (Btor *btor, BoolectorNode *node)
{
  BtorNode *exp, *simp;
  int res;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_TRAPI_UNFUN ("is_param", exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  simp = btor_simplify_exp (btor, exp);
  BTOR_ABORT_BOOLECTOR (!BTOR_IS_PARAM_NODE (BTOR_REAL_ADDR_NODE (simp)),
                        "given expression is not a parameter node");
  res = btor_is_bound_param_exp (btor, simp);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES (res, is_bound_param, node);
#endif
  BTOR_TRAPI_RETURN (res);
  return res;
}

int
boolector_is_fun (Btor *btor, BoolectorNode *node)
{
  int res;
  BtorNode *exp, *simp;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_TRAPI_UNFUN ("is_fun", exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  simp = btor_simplify_exp (btor, exp);
  res  = btor_is_fun_exp (btor, simp);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES (res, is_fun, BTOR_CLONED_EXP (exp));
#endif
  BTOR_TRAPI_RETURN (res);
  return res;
}

int
boolector_get_fun_arity (Btor *btor, BoolectorNode *node)
{
  int res;
  BtorNode *exp, *simp;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_TRAPI_UNFUN ("get_fun_arity", exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  simp = btor_simplify_exp (btor, exp);
  BTOR_ABORT_BOOLECTOR (!btor_is_fun_exp (btor, simp),
                        "given expression is not a function node");
  res = btor_get_fun_arity (btor, simp);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES (res, get_fun_arity, BTOR_CLONED_EXP (exp));
#endif
  BTOR_TRAPI_RETURN (res);
  return res;
}

int
boolector_is_args (Btor *btor, BoolectorNode *node)
{
  int res;
  BtorNode *exp, *simp;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_TRAPI_UNFUN ("is_args", exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  simp = btor_simplify_exp (btor, exp);
  res  = btor_is_args_exp (btor, simp);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES (res, is_args, BTOR_CLONED_EXP (exp));
#endif
  BTOR_TRAPI_RETURN (res);
  return res;
}

int
boolector_get_args_arity (Btor *btor, BoolectorNode *node)
{
  int res;
  BtorNode *exp, *simp;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_TRAPI_UNFUN ("get_args_arity", exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  simp = btor_simplify_exp (btor, exp);
  BTOR_ABORT_BOOLECTOR (!BTOR_IS_ARGS_NODE (BTOR_REAL_ADDR_NODE (simp)),
                        "given expression is not an argument node");
  res = btor_get_args_arity (btor, simp);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES (res, get_args_arity, BTOR_CLONED_EXP (exp));
#endif
  BTOR_TRAPI_RETURN (res);
  return res;
}

int
boolector_get_index_width (Btor *btor, BoolectorNode *n_array)
{
  int res;
  BtorNode *e_array, *simp_array;

  e_array = BTOR_IMPORT_BOOLECTOR_NODE (n_array);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e_array);
  BTOR_TRAPI_UNFUN ("get_index_width", e_array);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e_array);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e_array);
  simp_array = btor_simplify_exp (btor, e_array);
  BTOR_ABORT_BV_BOOLECTOR (simp_array);
  res = btor_get_index_exp_len (btor, simp_array);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES (res, get_index_width, BTOR_CLONED_EXP (e_array));
#endif
  BTOR_TRAPI_RETURN (res);
  return res;
}

int
boolector_fun_sort_check (Btor *btor,
                          int argc,
                          BoolectorNode **arg_nodes,
                          BoolectorNode *n_fun)
{
  BtorNode **args, *e_fun, *simp;
  char *strtrapi;
  int i, len, res;

  args  = BTOR_IMPORT_BOOLECTOR_NODE_ARRAY (arg_nodes);
  e_fun = BTOR_IMPORT_BOOLECTOR_NODE (n_fun);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e_fun);
  BTOR_ABORT_BOOLECTOR (argc < 1, "'argc' must not be < 1");
  BTOR_ABORT_BOOLECTOR (argc >= 1 && !args,
                        "no arguments given but argc defined > 0");

  len = 15 + 10 + argc * 20 + 20;
  BTOR_NEWN (btor->mm, strtrapi, len);
  sprintf (strtrapi, "fun_sort_check %d", argc);

  for (i = 0; i < argc; i++)
  {
    BTOR_ABORT_ARG_NULL_BOOLECTOR (args[i]);
    BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (args[i]);
    BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, args[i]);
    sprintf (
        strtrapi + strlen (strtrapi), NODE_FMT, BTOR_TRAPI_NODE_ID (args[i]));
  }
  sprintf (strtrapi + strlen (strtrapi), NODE_FMT, BTOR_TRAPI_NODE_ID (e_fun));
  BTOR_TRAPI (strtrapi);
  BTOR_DELETEN (btor->mm, strtrapi, len);
  simp = btor_simplify_exp (btor, e_fun);
  res  = btor_fun_sort_check (btor, argc, args, simp);
#ifndef NDEBUG
  BoolectorNode *carg_nodes[argc];
  for (i = 0; btor->clone && i < argc; i++)
    carg_nodes[i] = BTOR_CLONED_EXP (args[i]);
  BTOR_CHKCLONE_RES (
      res, fun_sort_check, argc, carg_nodes, BTOR_CLONED_EXP (e_fun));
#endif
  BTOR_TRAPI_RETURN (res);
  return res;
}

const char *
boolector_get_symbol_of_var (Btor *btor, BoolectorNode *node)
{
  const char *res;
  BtorNode *exp;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_TRAPI_UNFUN ("get_symbol_of_var", exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  res = (const char *) btor_get_symbol_exp (btor, exp);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_STR (res, get_symbol_of_var, BTOR_CLONED_EXP (exp));
#endif
  BTOR_TRAPI_RETURN_STR (res);
  return res;
}

BoolectorNode *
boolector_copy (Btor *btor, BoolectorNode *node)
{
  BtorNode *exp, *res;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_TRAPI_UNFUN ("copy", exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  btor->external_refs++;
  res = btor_copy_exp (btor, exp);
  BTOR_REAL_ADDR_NODE (res)->ext_refs += 1;
#ifndef NDEBUG
  BTOR_CHKCLONE_RES_PTR (res, copy, BTOR_CLONED_EXP (exp));
#endif
  BTOR_TRAPI_RETURN_NODE (res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

void
boolector_release (Btor *btor, BoolectorNode *node)
{
  BtorNode *exp;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_TRAPI_UNFUN ("release", exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  btor->external_refs--;
#ifndef NDEBUG
  BoolectorNode *cexp = BTOR_CLONED_EXP (exp);
#endif
  assert (BTOR_REAL_ADDR_NODE (exp)->ext_refs);
  BTOR_REAL_ADDR_NODE (exp)->ext_refs -= 1;
  btor_release_exp (btor, exp);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (release, cexp);
#endif
}

void
boolector_dump_btor_node (Btor *btor, FILE *file, BoolectorNode *node)
{
  // TODO TRAPI
  BtorNode *exp;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (file);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  btor_dump_btor_node (btor, file, exp);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (dump_btor_node, file, BTOR_CLONED_EXP (exp));
#endif
}

void
boolector_dump_btor (Btor *btor, FILE *file)
{
  BTOR_TRAPI ("dump_btor");
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (file);
  btor_dump_btor (btor, file);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (dump_btor, file);
#endif
}

void
boolector_dump_smt1_node (Btor *btor, FILE *file, BoolectorNode *node)
{
  // TODO TRAPI
  BtorNode *exp;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (file);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  btor_dump_smt1_nodes (btor, file, &exp, 1);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (dump_smt1_node, file, BTOR_CLONED_EXP (exp));
#endif
}

void
boolector_dump_smt1 (Btor *btor, FILE *file)
{
  BTOR_TRAPI ("dump_smt1");
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (file);
  btor_dump_smt1 (btor, file);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (dump_smt1, file);
#endif
}

void
boolector_dump_smt2_node (Btor *btor, FILE *file, BoolectorNode *node)
{
  // TODO TRAPI
  BtorNode *exp;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (file);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  btor_dump_smt2_nodes (btor, file, &exp, 1);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (dump_smt2_node, file, BTOR_CLONED_EXP (exp));
#endif
}

void
boolector_dump_smt2 (Btor *btor, FILE *file)
{
  BTOR_TRAPI ("dump_smt2");
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (file);
  btor_dump_smt2 (btor, file);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (dump_smt2, file);
#endif
}

void
boolector_assert (Btor *btor, BoolectorNode *node)
{
  BtorNode *exp, *simp;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI_UNFUN ("assert", exp);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  simp = btor_simplify_exp (btor, exp);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp);
  BTOR_ABORT_BOOLECTOR (BTOR_REAL_ADDR_NODE (simp)->len != 1,
                        "'exp' must have bit-width one");
  btor_assert_exp (btor, simp);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (assert, BTOR_CLONED_EXP (exp));
#endif
}

void
boolector_assume (Btor *btor, BoolectorNode *node)
{
  BtorNode *exp, *simp;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_TRAPI_UNFUN ("assume", exp);
  BTOR_ABORT_BOOLECTOR (!btor->options.inc_enabled,
                        "incremental usage has not been enabled");
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  /* Note: do not simplify constraint expression in order to prevent
   *       constraint expressions from not being added to btor->assumptions. */
  simp = BTOR_REAL_ADDR_NODE (exp)->simplified ? btor_simplify_exp (btor, exp)
                                               : exp;
  BTOR_ABORT_ARRAY_BOOLECTOR (simp);
  BTOR_ABORT_BOOLECTOR (BTOR_REAL_ADDR_NODE (simp)->len != 1,
                        "'exp' must have bit-width one");
  btor_assume_exp (btor, simp);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (assume, BTOR_CLONED_EXP (exp));
#endif
}

int
boolector_failed (Btor *btor, BoolectorNode *node)
{
  int res;
  BtorNode *exp;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_BOOLECTOR (
      btor->last_sat_result != BTOR_UNSAT,
      "cannot check failed assumptions if input formula is not UNSAT");
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_TRAPI_UNFUN ("failed", exp);
  BTOR_ABORT_BOOLECTOR (!btor->options.inc_enabled,
                        "incremental usage has not been enabled");
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  /* Note: do not simplify expression (see boolector_assume). */
  BTOR_ABORT_ARRAY_BOOLECTOR (exp);
  BTOR_ABORT_BOOLECTOR (BTOR_REAL_ADDR_NODE (exp)->len != 1,
                        "'exp' must have bit-width one");
  BTOR_ABORT_BOOLECTOR (!btor_is_assumption_exp (btor, exp),
                        "'exp' must be an assumption");
  res = btor_failed_exp (btor, exp);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES (res, failed, BTOR_CLONED_EXP (exp));
#endif
  BTOR_TRAPI_RETURN (res);
  return res;
}

int
boolector_sat (Btor *btor)
{
  int res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("sat");
  BTOR_ABORT_BOOLECTOR (
      !btor->options.inc_enabled && btor->btor_sat_btor_called > 0,
      "incremental usage has not been enabled."
      "'boolector_sat' may only be called once");
  res = btor_sat_btor (btor);
#ifndef NDEBUG
  BTOR_CHKCLONE_RES (res, sat);
#endif
  BTOR_TRAPI_RETURN (res);
  return res;
}

const char *
boolector_bv_assignment (Btor *btor, BoolectorNode *node)
{
  const char *ass;
  const char *res;
  BtorNode *exp, *simp;
  BtorBVAssignment *bvass;

  exp = BTOR_IMPORT_BOOLECTOR_NODE (node);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (exp);
  BTOR_TRAPI_UNFUN ("bv_assignment", exp);
  BTOR_ABORT_BOOLECTOR (
      btor->last_sat_result != BTOR_SAT,
      "cannot retrieve assignment if input formula is not SAT");
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (exp);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, exp);
  simp = btor_simplify_exp (btor, exp);
  BTOR_ABORT_ARRAY_BOOLECTOR (simp);
  BTOR_ABORT_BOOLECTOR (!btor->options.model_gen,
                        "model generation has not been enabled");
  ass   = btor_bv_assignment_str (btor, simp);
  bvass = btor_new_bv_assignment (btor->bv_assignments, (char *) ass);
  btor_release_bv_assignment_str (btor, (char *) ass);
  res = btor_get_bv_assignment_str (bvass);
#ifndef NDEBUG
  if (btor->clone)
  {
    const char *cloneres =
        boolector_bv_assignment (btor->clone, BTOR_CLONED_EXP (exp));
    assert (!strcmp (cloneres, res));
    bvass->cloned_assignment = cloneres;
    BTOR_CHKCLONE ();
  }
#endif
  BTOR_TRAPI_RETURN_PTR (res);
  return res;
}

void
boolector_free_bv_assignment (Btor *btor, const char *assignment)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("free_bv_assignment %p", assignment);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (assignment);
#ifndef NDEBUG
  char *cass;
  cass = (char *) btor_get_bv_assignment ((const char *) assignment)
             ->cloned_assignment;
#endif
  btor_release_bv_assignment (btor->bv_assignments, assignment);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (free_bv_assignment, cass);
#endif
}

void
boolector_array_assignment (Btor *btor,
                            BoolectorNode *n_array,
                            char ***indices,
                            char ***values,
                            int *size)
{
  int i;
  char **ind, **val;
  BtorNode *e_array, *simp;
  BtorArrayAssignment *arrass;

  e_array = BTOR_IMPORT_BOOLECTOR_NODE (n_array);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_ABORT_BOOLECTOR (
      btor->last_sat_result != BTOR_SAT,
      "cannot retrieve assignment if input formula is not SAT");
  BTOR_ABORT_ARG_NULL_BOOLECTOR (e_array);
  BTOR_TRAPI_UNFUN ("array_assignment", e_array);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (indices);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (values);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (size);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (e_array);
  BTOR_ABORT_IF_BTOR_DOES_NOT_MATCH (btor, e_array);
  simp = btor_simplify_exp (btor, e_array);
  BTOR_ABORT_BV_BOOLECTOR (simp);
  BTOR_ABORT_BOOLECTOR (!btor->options.model_gen,
                        "model generation has not been enabled");

  btor_array_assignment_str (btor, simp, &ind, &val, size);

  if (*size)
  {
    arrass =
        btor_new_array_assignment (btor->array_assignments, ind, val, *size);
    for (i = 0; i < *size; i++)
    {
      btor_release_bv_assignment_str (btor, ind[i]);
      btor_release_bv_assignment_str (btor, val[i]);
    }
    btor_free (btor->mm, ind, *size * sizeof (*ind));
    btor_free (btor->mm, val, *size * sizeof (*val));
    btor_get_array_assignment_indices_values (arrass, indices, values, *size);
  }
  else
    arrass = 0;  // remove warning

#ifndef NDEBUG
  if (btor->clone)
  {
    char **cindices, **cvalues;
    int csize;

    boolector_array_assignment (
        btor->clone, BTOR_CLONED_EXP (e_array), &cindices, &cvalues, &csize);
    assert (csize == *size);
    for (i = 0; i < *size; i++)
    {
      assert (!strcmp ((*indices)[i], cindices[i]));
      assert (!strcmp ((*values)[i], cvalues[i]));
    }
    if (arrass)
    {
      assert (*size);
      arrass->cloned_indices = cindices;
      arrass->cloned_values  = cvalues;
    }
    BTOR_CHKCLONE ();
  }
#endif
  /* special case: we treat out parameters as return values for btoruntrace */
  BTOR_TRAPI ("return %p %p %d", *indices, *values, *size);
}

void
boolector_free_array_assignment (Btor *btor,
                                 char **indices,
                                 char **values,
                                 int size)
{
  BtorArrayAssignment *arrass;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (btor);
  BTOR_TRAPI ("free_array_assignment %p %p %d", indices, values, size);
  BTOR_ABORT_BOOLECTOR (size < 0, "negative size");
  if (size)
  {
    BTOR_ABORT_ARG_NULL_BOOLECTOR (indices);
    BTOR_ABORT_ARG_NULL_BOOLECTOR (values);
  }
  else
  {
    BTOR_ABORT_BOOLECTOR (indices, "non zero 'indices' but 'size == 0'");
    BTOR_ABORT_BOOLECTOR (values, "non zero 'values' but 'size == 0'");
  }
  arrass = btor_get_array_assignment (
      (const char **) indices, (const char **) values, size);
  (void) arrass;
#ifndef NDEBUG
  char **cindices, **cvalues;
  cindices = arrass->cloned_indices;
  cvalues  = arrass->cloned_values;
#endif
  btor_release_array_assignment (
      btor->array_assignments, indices, values, size);
#ifndef NDEBUG
  BTOR_CHKCLONE_NORES (free_array_assignment, cindices, cvalues, size);
#endif
}
