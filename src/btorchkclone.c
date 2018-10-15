/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2013-2018 Aina Niemetz.
 *  Copyright (C) 2013-2017 Mathias Preiner.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

/*------------------------------------------------------------------------*/
#ifndef NDEBUG
/*------------------------------------------------------------------------*/

#include "btorbv.h"
#include "btorcore.h"
#include "btoropt.h"
#include "btorslv.h"
#include "btorslvaigprop.h"
#include "btorslvfun.h"
#include "btorslvprop.h"
#include "btorslvsls.h"
#include "utils/btorhashint.h"
#include "utils/btorhashptr.h"

#include "btorchkclone.h"

/*------------------------------------------------------------------------*/

#define BTOR_CHKCLONE_EXPID(exp, clone)                                        \
  do                                                                           \
  {                                                                            \
    assert (btor_node_real_addr (exp)->id == btor_node_real_addr (clone)->id); \
  } while (0)

/*------------------------------------------------------------------------*/

static int32_t
cmp_data_as_int (const BtorHashTableData *d1, const BtorHashTableData *d2)
{
  assert (d1);
  assert (d2);

  return d1->as_int - d2->as_int;
}

static int32_t
cmp_data_as_dbl (const BtorHashTableData *d1, const BtorHashTableData *d2)
{
  assert (d1);
  assert (d2);

  return d1->as_dbl == d2->as_dbl ? 0 : (d1->as_dbl > d2->as_dbl ? 1 : -1);
}

static int32_t
cmp_data_as_bv_ptr (const BtorHashTableData *d1, const BtorHashTableData *d2)
{
  assert (d1);
  assert (d2);

  return btor_bv_compare (d1->as_ptr, d2->as_ptr);
}

static int32_t
cmp_data_as_sls_constr_data_ptr (const BtorHashTableData *d1,
                                 const BtorHashTableData *d2)
{
  assert (d1);
  assert (d2);

  BtorSLSConstrData *scd1, *scd2;

  scd1 = (BtorSLSConstrData *) d1->as_ptr;
  scd2 = (BtorSLSConstrData *) d2->as_ptr;
  if (scd1->weight != scd2->weight) return 1;
  if (scd1->selected != scd2->selected) return 1;
  return 0;
}

static inline void
chkclone_int_hash_table (BtorIntHashTable *table, BtorIntHashTable *ctable)
{
  size_t i;

  if (!table)
  {
    assert (!ctable);
    return;
  }

  assert (table->size == ctable->size);
  assert (table->count == ctable->count);
  for (i = 0; i < table->size; i++)
  {
    assert (i < ctable->size);
    if (!table->keys[i])
    {
      assert (!ctable->keys[i]);
      continue;
    }
    assert (table->keys[i] == ctable->keys[i]);
  }
  assert (i >= ctable->size);
}

static inline void
chkclone_int_hash_map (BtorIntHashTable *map,
                       BtorIntHashTable *cmap,
                       int32_t (*cmp_data) (const BtorHashTableData *,
                                            const BtorHashTableData *))
{
  size_t i;

  if (!map)
  {
    assert (!cmap);
    return;
  }

  assert (map->size == cmap->size);
  assert (map->count == cmap->count);
  for (i = 0; i < map->size; i++)
  {
    assert (i < cmap->size);
    if (!map->keys[i])
    {
      assert (!cmap->keys[i]);
      continue;
    }
    assert (map->keys[i] == cmap->keys[i]);
    if (cmp_data) assert (!cmp_data (&map->data[i], &cmap->data[i]));
  }
  assert (i >= cmap->size);
}

static inline void
chkclone_node_ptr_hash_table (BtorPtrHashTable *table,
                              BtorPtrHashTable *ctable,
                              int32_t (*cmp_data) (const BtorHashTableData *,
                                                   const BtorHashTableData *))
{
  BtorPtrHashTableIterator it, cit;

  if (!table)
  {
    assert (!ctable);
    return;
  }

  assert (table->size == ctable->size);
  assert (table->count == ctable->count);
  assert (table->hash == ctable->hash);
  assert (table->cmp == ctable->cmp);
  btor_iter_hashptr_init (&it, table);
  btor_iter_hashptr_init (&cit, ctable);
  while (btor_iter_hashptr_has_next (&it))
  {
    assert (btor_iter_hashptr_has_next (&cit));
    if (cmp_data) assert (!cmp_data (&it.bucket->data, &cit.bucket->data));
    BTOR_CHKCLONE_EXPID (btor_iter_hashptr_next (&it),
                         btor_iter_hashptr_next (&cit));
  }
  assert (!btor_iter_hashptr_has_next (&cit));
}

/*------------------------------------------------------------------------*/

static void
chkclone_mem (Btor *btor, Btor *clone)
{
  assert (btor);
  assert (clone);
  assert (btor->mm);
  assert (clone->mm);
  assert (btor->mm->allocated
              - (btor->msg->prefix
                     ? (strlen (btor->msg->prefix) + 1) * sizeof (char)
                     : 0)
          == clone->mm->allocated
                 - (clone->msg->prefix
                        ? (strlen (clone->msg->prefix) + 1) * sizeof (char)
                        : 0));
  assert (btor->mm->sat_allocated == clone->mm->sat_allocated);
  /* Note: both maxallocated and sat_maxallocated may differ! */
}

/*------------------------------------------------------------------------*/

#define BTOR_CHKCLONE_STATE(field)        \
  do                                      \
  {                                       \
    assert (clone->field == btor->field); \
  } while (0)

static void
chkclone_state (Btor *btor, Btor *clone)
{
  assert (btor);
  assert (clone);

  BTOR_CHKCLONE_STATE (rec_rw_calls);
  BTOR_CHKCLONE_STATE (valid_assignments);
  BTOR_CHKCLONE_STATE (vis_idx);
  BTOR_CHKCLONE_STATE (inconsistent);
  BTOR_CHKCLONE_STATE (found_constraint_false);
  BTOR_CHKCLONE_STATE (external_refs);
  BTOR_CHKCLONE_STATE (btor_sat_btor_called);
  BTOR_CHKCLONE_STATE (last_sat_result);
}

/*------------------------------------------------------------------------*/

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
chkclone_stats (Btor *btor, Btor *clone)
{
  assert (btor);
  assert (clone);

#ifndef NDEBUG
  BtorPtrHashTableIterator it, cit;
  BtorHashTableData *data, *cdata;
  char *key, *ckey;
#endif

  BTOR_CHKCLONE_STATS (max_rec_rw_calls);
  BTOR_CHKCLONE_STATS (var_substitutions);
  BTOR_CHKCLONE_STATS (uf_substitutions);
  BTOR_CHKCLONE_STATS (ec_substitutions);
  BTOR_CHKCLONE_STATS (linear_equations);
  BTOR_CHKCLONE_STATS (gaussian_eliminations);
  BTOR_CHKCLONE_STATS (eliminated_slices);
  BTOR_CHKCLONE_STATS (skeleton_constraints);
  BTOR_CHKCLONE_STATS (adds_normalized);
  BTOR_CHKCLONE_STATS (ands_normalized);
  BTOR_CHKCLONE_STATS (muls_normalized);
  BTOR_CHKCLONE_STATS (muls_normalized);
  BTOR_CHKCLONE_STATS (ackermann_constraints);
  BTOR_CHKCLONE_STATS (bv_uc_props);
  BTOR_CHKCLONE_STATS (fun_uc_props);
  BTOR_CHKCLONE_STATS (lambdas_merged);
  BTOR_CHKCLONE_STATS (expressions);
  BTOR_CHKCLONE_STATS (clone_calls);
  BTOR_CHKCLONE_STATS (node_bytes_alloc);
  BTOR_CHKCLONE_STATS (beta_reduce_calls);

  BTOR_CHKCLONE_CONSTRAINTSTATS (constraints, varsubst);
  BTOR_CHKCLONE_CONSTRAINTSTATS (constraints, embedded);
  BTOR_CHKCLONE_CONSTRAINTSTATS (constraints, unsynthesized);
  BTOR_CHKCLONE_CONSTRAINTSTATS (constraints, synthesized);
  BTOR_CHKCLONE_CONSTRAINTSTATS (oldconstraints, varsubst);
  BTOR_CHKCLONE_CONSTRAINTSTATS (oldconstraints, embedded);
  BTOR_CHKCLONE_CONSTRAINTSTATS (oldconstraints, unsynthesized);
  BTOR_CHKCLONE_CONSTRAINTSTATS (oldconstraints, synthesized);

#ifndef NDEBUG
  assert (btor->stats.rw_rules_applied && clone->stats.rw_rules_applied);
  assert (btor->stats.rw_rules_applied->size
          == clone->stats.rw_rules_applied->size);
  assert (btor->stats.rw_rules_applied->count
          == clone->stats.rw_rules_applied->count);
  assert (btor->stats.rw_rules_applied->hash
          == clone->stats.rw_rules_applied->hash);
  assert (btor->stats.rw_rules_applied->cmp
          == clone->stats.rw_rules_applied->cmp);
  btor_iter_hashptr_init (&it, btor->stats.rw_rules_applied);
  btor_iter_hashptr_init (&cit, clone->stats.rw_rules_applied);
  while (btor_iter_hashptr_has_next (&it))
  {
    assert (btor_iter_hashptr_has_next (&cit));
    data  = &it.bucket->data;
    cdata = &cit.bucket->data;
    key   = (char *) btor_iter_hashptr_next (&it);
    ckey  = (char *) btor_iter_hashptr_next (&cit);
    assert (!strcmp (key, ckey));
    assert (data->as_int == cdata->as_int);
  }
  assert (!btor_iter_hashptr_has_next (&cit));
#endif

  BTOR_CHKCLONE_STATS (expressions);
  BTOR_CHKCLONE_STATS (node_bytes_alloc);
  BTOR_CHKCLONE_STATS (beta_reduce_calls);
}

/*------------------------------------------------------------------------*/

static void
chkclone_opts (Btor *btor, Btor *clone)
{
  assert (btor);
  assert (clone);

  BtorOpt *opt, *copt;
  BtorOption o;

  assert (btor->options);
  assert (clone->options);

  for (o = btor_opt_first (btor); btor_opt_is_valid (btor, o);
       o = btor_opt_next (btor, o))
  {
    opt  = &btor->options[o];
    copt = &clone->options[o];
    assert (opt->internal == copt->internal);
    /* Note: auto_cleanup.val = 1 in clone! */
    if (o != BTOR_OPT_AUTO_CLEANUP && o != BTOR_OPT_AUTO_CLEANUP_INTERNAL)
      assert (opt->val == copt->val);
    assert (opt->dflt == copt->dflt);
    assert (opt->min == copt->min);
    assert (opt->max == copt->max);
    assert (opt->lng && !strcmp (opt->lng, copt->lng));
    assert ((!opt->shrt && !copt->shrt)
            || (opt->shrt && !strcmp (opt->shrt, copt->shrt)));
    assert ((!opt->desc && !copt->desc)
            || (opt->desc && !strcmp (opt->desc, copt->desc)));
    assert ((!opt->valstr && !copt->valstr)
            || (opt->valstr && !strcmp (opt->valstr, copt->valstr)));
  }
}

/*------------------------------------------------------------------------*/

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
    assert (btor_aig_is_const (real_aig->field)            \
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
chkclone_aig (BtorAIG *aig, BtorAIG *clone)
{
  int32_t i;
  BtorAIG *real_aig, *real_clone;

  real_aig   = BTOR_REAL_ADDR_AIG (aig);
  real_clone = BTOR_REAL_ADDR_AIG (clone);
  assert ((real_aig == BTOR_AIG_FALSE && real_clone == BTOR_AIG_FALSE)
          || real_aig != real_clone);

  if (real_aig != BTOR_AIG_FALSE)
  {
    BTOR_CHKCLONE_AIG (id);
    BTOR_CHKCLONE_AIG (refs);
    BTOR_CHKCLONE_AIG (next);
    BTOR_CHKCLONE_AIG (cnf_id);
    BTOR_CHKCLONE_AIG (mark);
    BTOR_CHKCLONE_AIG (is_var);
    BTOR_CHKCLONE_AIG (local);
    if (!real_aig->is_var)
      for (i = 0; i < 2; i++) BTOR_CHKCLONE_AIG (children[i]);
  }
}

static inline void
chkclone_aig_unique_table (Btor *btor, Btor *clone)
{
  uint32_t i;
  BtorAIGUniqueTable *btable, *ctable;

  btable = &btor_get_aig_mgr (btor)->table;
  ctable = &btor_get_aig_mgr (clone)->table;
  assert (btable != ctable);

  assert (btable->size == ctable->size);
  assert (btable->num_elements == ctable->num_elements);

  for (i = 0; i < btable->size; i++)
    assert (btable->chains[i] == ctable->chains[i]);
}

static inline void
chkclone_aig_id_table (Btor *btor, Btor *clone)
{
  uint32_t i;
  BtorAIGPtrStack *btable, *ctable;

  btable = &btor_get_aig_mgr (btor)->id2aig;
  ctable = &btor_get_aig_mgr (clone)->id2aig;
  assert (btable != ctable);

  for (i = 0; i < BTOR_COUNT_STACK (*btable); i++)
    chkclone_aig (btable->start[i], ctable->start[i]);
}

static inline void
chkclone_aig_cnf_id_table (Btor *btor, Btor *clone)
{
  uint32_t i;
  BtorIntStack *btable, *ctable;

  btable = &btor_get_aig_mgr (btor)->cnfid2aig;
  ctable = &btor_get_aig_mgr (clone)->cnfid2aig;
  assert (btable != ctable);

  for (i = 0; i < BTOR_SIZE_STACK (*btable); i++)
    assert (btable->start[i] == ctable->start[i]);
}

/*------------------------------------------------------------------------*/

#define BTOR_CHKCLONE_EXP(field)                  \
  do                                              \
  {                                               \
    assert (real_exp->field == real_cexp->field); \
  } while (0)

#define BTOR_CHKCLONE_EXPPTRID(field)                               \
  do                                                                \
  {                                                                 \
    if (!real_exp->field)                                           \
    {                                                               \
      assert (!real_cexp->field);                                   \
      break;                                                        \
    }                                                               \
    assert (real_exp->field != real_cexp->field);                   \
    BTOR_CHKCLONE_EXPID (real_exp->field, real_cexp->field);        \
    assert (btor_node_real_addr (real_exp->field)->btor == btor);   \
    assert (btor_node_real_addr (real_cexp->field)->btor == clone); \
  } while (0)

#define BTOR_CHKCLONE_EXPPTRINV(field)                    \
  do                                                      \
  {                                                       \
    assert (btor_node_is_inverted (real_exp->field)       \
            == btor_node_is_inverted (real_cexp->field)); \
  } while (0)

#define BTOR_CHKCLONE_EXPPTRTAG(field)                \
  do                                                  \
  {                                                   \
    assert (btor_node_get_tag (real_exp->field)       \
            == btor_node_get_tag (real_cexp->field)); \
  } while (0)

void
btor_chkclone_exp (Btor *btor,
                   Btor *clone,
                   const BtorNode *exp,
                   const BtorNode *cexp)
{
  assert (btor);
  assert (exp);
  assert (clone);
  assert (cexp);
  assert (btor != clone);
  assert (exp != cexp);
  assert ((!btor_node_is_inverted (exp) && !btor_node_is_inverted (cexp))
          || (btor_node_is_inverted (exp) && btor_node_is_inverted (cexp)));

  uint32_t i;
  BtorNode *real_exp, *real_cexp, *e, *ce;
  BtorPtrHashTableIterator it, cit;

  real_exp  = btor_node_real_addr (exp);
  real_cexp = btor_node_real_addr (cexp);
  assert (real_exp != real_cexp);
  assert (cexp);
  assert (real_exp->id == real_cexp->id);
  assert (real_exp->btor == btor);
  assert (real_cexp->btor == clone);

  BTOR_CHKCLONE_EXP (kind);
  BTOR_CHKCLONE_EXP (constraint);
  BTOR_CHKCLONE_EXP (erased);
  BTOR_CHKCLONE_EXP (disconnected);
  BTOR_CHKCLONE_EXP (unique);
  BTOR_CHKCLONE_EXP (bytes);
  BTOR_CHKCLONE_EXP (parameterized);
  BTOR_CHKCLONE_EXP (lambda_below);

  if (btor_node_is_bv_const (real_exp))
  {
    assert (btor_node_bv_const_get_bits (real_exp)->width
            == btor_node_bv_const_get_bits (real_cexp)->width);
    assert (btor_bv_compare (btor_node_bv_const_get_bits (real_exp),
                             btor_node_bv_const_get_bits (real_cexp))
            == 0);
    if (btor_node_bv_const_get_invbits (real_exp))
    {
      assert (btor_node_bv_const_get_invbits (real_exp)->width
              == btor_node_bv_const_get_invbits (real_cexp)->width);
      assert (btor_bv_compare (btor_node_bv_const_get_invbits (real_exp),
                               btor_node_bv_const_get_invbits (real_cexp))
              == 0);
    }
  }
  else
  {
    assert ((real_exp->av && real_cexp->av)
            || (!real_exp->av && !real_cexp->av));
  }

  BTOR_CHKCLONE_EXP (id);
  BTOR_CHKCLONE_EXP (refs);
  BTOR_CHKCLONE_EXP (ext_refs);
  BTOR_CHKCLONE_EXP (parents);
  BTOR_CHKCLONE_EXP (arity);

  if (!btor_node_is_fun (real_exp))
  {
    if (real_exp->av)
    {
      assert (real_cexp->av);
      assert (real_exp->av->width == real_cexp->av->width);
      for (i = 0; i < real_exp->av->width; i++)
        chkclone_aig (real_exp->av->aigs[i], real_cexp->av->aigs[i]);
    }
    else
      assert (real_exp->av == real_cexp->av);
  }
  else if (real_exp->rho)
    chkclone_node_ptr_hash_table (real_exp->rho, real_cexp->rho, 0);

  BTOR_CHKCLONE_EXPPTRID (next);
  BTOR_CHKCLONE_EXPPTRID (simplified);
  BTOR_CHKCLONE_EXPPTRID (first_parent);
  BTOR_CHKCLONE_EXPPTRID (last_parent);
  BTOR_CHKCLONE_EXPPTRINV (simplified);
  BTOR_CHKCLONE_EXPPTRTAG (first_parent);
  BTOR_CHKCLONE_EXPPTRTAG (last_parent);

  if (btor_node_is_proxy (real_exp)) return;

  if (!btor_node_is_bv_const (real_exp))
  {
    if (!btor_node_is_bv_var (real_exp) && !btor_node_is_uf (real_exp)
        && !btor_node_is_param (real_exp))
    {
      if (real_exp->arity)
      {
        for (i = 0; i < real_exp->arity; i++) BTOR_CHKCLONE_EXPPTRINV (e[i]);
      }
    }

    if (btor_node_is_bv_slice (real_exp))
    {
      assert (btor_node_bv_slice_get_upper (real_exp)
              == btor_node_bv_slice_get_upper (real_cexp));
      assert (btor_node_bv_slice_get_lower (real_exp)
              == btor_node_bv_slice_get_lower (real_cexp));
    }

    for (i = 0; i < real_exp->arity; i++)
    {
      BTOR_CHKCLONE_EXPPTRID (prev_parent[i]);
      BTOR_CHKCLONE_EXPPTRID (next_parent[i]);
      BTOR_CHKCLONE_EXPPTRTAG (prev_parent[i]);
      BTOR_CHKCLONE_EXPPTRTAG (next_parent[i]);
    }
  }

#if 0
  if (btor_node_is_fun (real_exp))
    {
      BTOR_CHKCLONE_EXP (index_len);
      BTOR_CHKCLONE_EXPPTRID (first_aeq_acond_parent);
      BTOR_CHKCLONE_EXPPTRID (last_aeq_acond_parent);
      BTOR_CHKCLONE_EXPPTAG (first_aeq_acond_parent);
      BTOR_CHKCLONE_EXPPTAG (last_aeq_acond_parent);

      if (!BTOR_IS_ARRAY_VAR_NODE (real_exp))
	{
	  for (i = 0; i < real_exp->arity; i++)
	    {
	      BTOR_CHKCLONE_EXPPTRID (prev_aeq_acond_parent[i]);
	      BTOR_CHKCLONE_EXPPTRID (next_aeq_acond_parent[i]);
	      BTOR_CHKCLONE_EXPPTRTAG (prev_aeq_acond_parent[i]);
	      BTOR_CHKCLONE_EXPPTRTAG (next_aeq_acond_parent[i]);
	    }
	}
    }
#endif

  if (btor_node_is_param (real_exp))
  {
    if (btor_node_param_is_bound (real_exp))
    {
      assert (btor_node_param_get_binder (real_exp)
              != btor_node_param_get_binder (real_cexp));
      BTOR_CHKCLONE_EXPID (btor_node_param_get_binder (real_exp),
                           btor_node_param_get_binder (real_cexp));
    }
    else
      assert (!btor_node_param_is_bound (real_cexp));

    if (((BtorParamNode *) real_exp)->assigned_exp)
    {
      assert (((BtorParamNode *) real_exp)->assigned_exp
              != ((BtorParamNode *) real_cexp)->assigned_exp);
      BTOR_CHKCLONE_EXPID (((BtorParamNode *) real_exp)->assigned_exp,
                           ((BtorParamNode *) real_cexp)->assigned_exp);
    }
    else
      assert (!((BtorParamNode *) real_cexp)->assigned_exp);
  }

  if (btor_node_is_lambda (real_exp))
  {
    if (btor_node_lambda_get_static_rho (real_exp))
    {
      btor_iter_hashptr_init (&it, btor_node_lambda_get_static_rho (real_exp));
      btor_iter_hashptr_init (&cit,
                              btor_node_lambda_get_static_rho (real_cexp));
      while (btor_iter_hashptr_has_next (&it))
      {
        assert (btor_iter_hashptr_has_next (&cit));
        e  = btor_iter_hashptr_next (&it);
        ce = btor_iter_hashptr_next (&cit);
        if (e)
        {
          assert (ce);
          assert (e != ce);
          BTOR_CHKCLONE_EXPID (e, ce);
        }
        else
          assert (!ce);
      }
      assert (!btor_iter_hashptr_has_next (&cit));
    }

#if 0
      if (((BtorLambdaNode *) real_exp)->head)
	{
	  assert (((BtorLambdaNode *) real_exp)->head
		  != ((BtorLambdaNode *) real_cexp)->head);
	  BTOR_CHKCLONE_EXPID (((BtorLambdaNode *) real_exp)->head,
			       ((BtorLambdaNode *) real_cexp)->head);
	}
      else
	assert (!((BtorLambdaNode *) real_cexp)->head);
#endif

    if (((BtorLambdaNode *) real_exp)->body)
    {
      assert (((BtorLambdaNode *) real_exp)->body
              != ((BtorLambdaNode *) real_cexp)->body);
      BTOR_CHKCLONE_EXPID (((BtorLambdaNode *) real_exp)->body,
                           ((BtorLambdaNode *) real_cexp)->body);
    }
    else
      assert (!((BtorLambdaNode *) real_cexp)->body);
  }
}

/*------------------------------------------------------------------------*/

static inline void
chkclone_node_ptr_stack (BtorNodePtrStack *stack, BtorNodePtrStack *cstack)
{
  uint32_t i;

  assert (BTOR_COUNT_STACK (*stack) == BTOR_COUNT_STACK (*cstack));
  for (i = 0; i < BTOR_COUNT_STACK (*stack); i++)
  {
    if (!BTOR_PEEK_STACK (*stack, i))
    {
      assert (!BTOR_PEEK_STACK (*cstack, i));
      continue;
    }

    BTOR_CHKCLONE_EXPID (BTOR_PEEK_STACK (*stack, i),
                         BTOR_PEEK_STACK (*cstack, i));
  }
}

/*------------------------------------------------------------------------*/

static inline void
chkclone_node_id_table (Btor *btor, Btor *clone)
{
  uint32_t i;
  BtorNodePtrStack *btable, *ctable;

  btable = &btor->nodes_id_table;
  ctable = &clone->nodes_id_table;
  assert (btable != ctable);

  assert (BTOR_COUNT_STACK (*btable) == BTOR_COUNT_STACK (*ctable));

  for (i = 0; i < BTOR_COUNT_STACK (*btable); i++)
  {
    if (!BTOR_PEEK_STACK (*btable, i))
    {
      assert (!BTOR_PEEK_STACK (*ctable, i));
      continue;
    }

    btor_chkclone_exp (btor,
                       clone,
                       BTOR_PEEK_STACK (*btable, i),
                       BTOR_PEEK_STACK (*ctable, i));
  }
}

/*------------------------------------------------------------------------*/

/* Note: no need to check next pointers here as we catch all of them when
 *	 traversing through nodes id table. */
static inline void
chkclone_node_unique_table (Btor *btor, Btor *clone)
{
  uint32_t i;
  BtorNodeUniqueTable *btable, *ctable;

  btable = &btor->nodes_unique_table;
  ctable = &clone->nodes_unique_table;
  assert (btable != ctable);
  assert (btable->size == ctable->size);
  assert (btable->num_elements == ctable->num_elements);

  for (i = 0; i < btable->size; i++)
  {
    if (!btable->chains[i])
    {
      assert (!ctable->chains[i]);
      continue;
    }
    BTOR_CHKCLONE_EXPID (btable->chains[i], ctable->chains[i]);
  }
}

/*------------------------------------------------------------------------*/

static void
chkclone_assignment_lists (Btor *btor, Btor *clone)
{
  BtorBVAss *bvass, *cbvass;
  BtorFunAss *funass, *cfunass;
  char **ind, **val, **cind, **cval;
  uint32_t i;

  assert (btor->bv_assignments->count == clone->bv_assignments->count);

  for (bvass = btor->bv_assignments->first,
      cbvass = clone->bv_assignments->first;
       bvass;
       bvass = bvass->next, cbvass = cbvass->next)
  {
    assert (cbvass);
    assert (
        !strcmp (btor_ass_get_bv_str (bvass), btor_ass_get_bv_str (cbvass)));
  }

  assert (btor->fun_assignments->count == clone->fun_assignments->count);

  for (funass = btor->fun_assignments->first,
      cfunass = clone->fun_assignments->first;
       funass;
       funass = funass->next, cfunass = cfunass->next)
  {
    assert (cfunass);
    assert (funass->size == cfunass->size);
    btor_ass_get_fun_indices_values (funass, &ind, &val, funass->size);
    btor_ass_get_fun_indices_values (cfunass, &cind, &cval, cfunass->size);
    for (i = 0; i < funass->size; i++)
    {
      assert (!strcmp (ind[i], cind[i]));
      assert (!strcmp (val[i], cval[i]));
    }
  }
}

/*------------------------------------------------------------------------*/

static void
chkclone_tables (Btor *btor, Btor *clone)
{
  BtorPtrHashTableIterator pit, cpit, npit, cnpit;
  BtorIntHashTableIterator iit, ciit;
  char *sym, *csym;

  if (!btor->symbols)
    assert (!clone->symbols);
  else
  {
    assert (clone->symbols);
    assert (btor->symbols->size == clone->symbols->size);
    assert (btor->symbols->count == clone->symbols->count);
    assert (btor->symbols->hash == clone->symbols->hash);
    assert (btor->symbols->cmp == clone->symbols->cmp);
    assert (!btor->symbols->first || clone->symbols->first);
    btor_iter_hashptr_init (&pit, btor->symbols);
    btor_iter_hashptr_init (&cpit, clone->symbols);
    while (btor_iter_hashptr_has_next (&pit))
    {
      assert (btor_iter_hashptr_has_next (&cpit));
      assert (!strcmp ((char *) btor_iter_hashptr_next (&pit),
                       (char *) btor_iter_hashptr_next (&cpit)));
    }
    assert (!btor_iter_hashptr_has_next (&cpit));
  }

  if (!btor->node2symbol)
    assert (!clone->node2symbol);
  else
  {
    assert (clone->node2symbol);
    assert (btor->node2symbol->size == clone->node2symbol->size);
    assert (btor->node2symbol->count == clone->node2symbol->count);
    assert (btor->node2symbol->hash == clone->node2symbol->hash);
    assert (btor->node2symbol->cmp == clone->node2symbol->cmp);
    assert (!btor->node2symbol->first || clone->node2symbol->first);
    btor_iter_hashptr_init (&pit, btor->node2symbol);
    btor_iter_hashptr_init (&cpit, clone->node2symbol);
    while (btor_iter_hashptr_has_next (&pit))
    {
      assert (btor_iter_hashptr_has_next (&cpit));
      sym  = pit.bucket->data.as_str;
      csym = cpit.bucket->data.as_str;
      assert (sym != csym);
      assert (!strcmp (sym, csym));
      assert (btor_hashptr_table_get (btor->symbols, sym));
      assert (btor_hashptr_table_get (clone->symbols, sym));
      BTOR_CHKCLONE_EXPID (btor_iter_hashptr_next (&pit),
                           btor_iter_hashptr_next (&cpit));
    }
    assert (!btor_iter_hashptr_has_next (&cpit));
  }

  chkclone_node_ptr_hash_table (btor->bv_vars, clone->bv_vars, 0);
  chkclone_node_ptr_hash_table (btor->lambdas, clone->lambdas, 0);
  chkclone_node_ptr_hash_table (btor->feqs, clone->feqs, 0);
  chkclone_node_ptr_hash_table (btor->substitutions, clone->substitutions, 0);
  chkclone_node_ptr_hash_table (
      btor->varsubst_constraints, clone->varsubst_constraints, 0);
  chkclone_node_ptr_hash_table (
      btor->embedded_constraints, clone->embedded_constraints, 0);
  chkclone_node_ptr_hash_table (
      btor->unsynthesized_constraints, clone->unsynthesized_constraints, 0);
  chkclone_node_ptr_hash_table (
      btor->synthesized_constraints, clone->synthesized_constraints, 0);
  chkclone_node_ptr_hash_table (btor->assumptions, clone->assumptions, 0);
  chkclone_node_ptr_hash_table (btor->var_rhs, clone->var_rhs, 0);
  chkclone_node_ptr_hash_table (btor->fun_rhs, clone->fun_rhs, 0);

  if (!btor->parameterized)
    assert (!clone->parameterized);
  else
  {
    assert (clone->parameterized);
    assert (btor->parameterized->size == clone->parameterized->size);
    assert (btor->parameterized->count == clone->parameterized->count);
    assert (btor->parameterized->hash == clone->parameterized->hash);
    assert (btor->parameterized->cmp == clone->parameterized->cmp);
    assert (!btor->parameterized->first || clone->parameterized->first);
    btor_iter_hashptr_init (&pit, btor->parameterized);
    btor_iter_hashptr_init (&cpit, clone->parameterized);
    while (btor_iter_hashptr_has_next (&pit))
    {
      assert (btor_iter_hashptr_has_next (&cpit));
      chkclone_int_hash_table ((BtorIntHashTable *) pit.bucket->data.as_ptr,
                               (BtorIntHashTable *) cpit.bucket->data.as_ptr);
      BTOR_CHKCLONE_EXPID (btor_iter_hashptr_next (&pit),
                           btor_iter_hashptr_next (&cpit));
    }
    assert (!btor_iter_hashptr_has_next (&cpit));
  }

  if (!btor->bv_model)
    assert (!clone->bv_model);
  else
  {
    assert (clone->bv_model);
    assert (btor->bv_model->size == clone->bv_model->size);
    assert (btor->bv_model->count == clone->bv_model->count);
    btor_iter_hashint_init (&iit, btor->bv_model);
    btor_iter_hashint_init (&ciit, clone->bv_model);
    while (btor_iter_hashint_has_next (&iit))
    {
      assert (btor_iter_hashint_has_next (&ciit));
      assert (btor->bv_model->data[iit.cur_pos].as_ptr);
      assert (clone->bv_model->data[ciit.cur_pos].as_ptr);
      assert (!btor_bv_compare (btor->bv_model->data[iit.cur_pos].as_ptr,
                                clone->bv_model->data[ciit.cur_pos].as_ptr));
      assert (btor_iter_hashint_next (&iit) == btor_iter_hashint_next (&ciit));
    }
    assert (!btor_iter_hashint_has_next (&ciit));
  }

  if (!btor->fun_model)
    assert (!clone->fun_model);
  else
  {
    assert (clone->fun_model);
    assert (btor->fun_model->size == clone->fun_model->size);
    assert (btor->fun_model->count == clone->fun_model->count);
    btor_iter_hashint_init (&iit, btor->fun_model);
    btor_iter_hashint_init (&ciit, clone->fun_model);
    while (btor_iter_hashint_has_next (&iit))
    {
      assert (btor_iter_hashint_has_next (&ciit));
      assert (btor->fun_model->data[iit.cur_pos].as_ptr);
      assert (clone->fun_model->data[ciit.cur_pos].as_ptr);
      btor_iter_hashptr_init (
          &npit,
          (BtorPtrHashTable *) btor->fun_model->data[iit.cur_pos].as_ptr);
      btor_iter_hashptr_init (
          &cnpit,
          (BtorPtrHashTable *) clone->fun_model->data[ciit.cur_pos].as_ptr);
      while (btor_iter_hashptr_has_next (&npit))
      {
        assert (btor_iter_hashptr_has_next (&cnpit));
        assert (!btor_bv_compare ((BtorBitVector *) npit.bucket->data.as_ptr,
                                  (BtorBitVector *) cnpit.bucket->data.as_ptr));
        assert (!btor_bv_compare_tuple ((BtorBitVectorTuple *) npit.cur,
                                        (BtorBitVectorTuple *) cnpit.cur));
        (void) btor_iter_hashptr_next (&npit);
        (void) btor_iter_hashptr_next (&cnpit);
      }
      assert (!btor_iter_hashptr_has_next (&cnpit));
      assert (btor_iter_hashint_next (&iit) == btor_iter_hashint_next (&ciit));
    }
    assert (!btor_iter_hashint_has_next (&ciit));
  }
}

/*------------------------------------------------------------------------*/

void
btor_chkclone_sort (Btor *btor,
                    Btor *clone,
                    const BtorSort *sort,
                    const BtorSort *csort)
{
  assert (btor);
  assert (clone);
  assert (btor != clone);
  assert (sort->id == sort->id);
  assert (sort->kind == sort->kind);
  assert (sort->refs == sort->refs);
  assert (sort->ext_refs == sort->ext_refs);
  assert (sort->parents == sort->parents);
  assert (sort->btor == btor);
  assert (csort->btor == clone);

  uint32_t i;

  switch (sort->kind)
  {
    case BTOR_BITVEC_SORT:
      assert (sort->bitvec.width == csort->bitvec.width);
      break;

    case BTOR_ARRAY_SORT:
      assert (sort->array.index->id == csort->array.index->id);
      assert (sort->array.element->id == csort->array.element->id);
      break;

    case BTOR_FUN_SORT:
      assert (sort->fun.arity == csort->fun.arity);
      assert (sort->fun.domain->id == csort->fun.domain->id);
      assert (sort->fun.codomain->id == csort->fun.codomain->id);
      break;

    case BTOR_TUPLE_SORT:
      assert (sort->tuple.num_elements == csort->tuple.num_elements);
      for (i = 0; i < sort->tuple.num_elements; i++)
        assert (sort->tuple.elements[i]->id == csort->tuple.elements[i]->id);
      break;

    case BTOR_LST_SORT:
      assert (sort->lst.head->id == csort->lst.head->id);
      assert (sort->lst.tail->id == csort->lst.tail->id);
      break;

    default: break;
  }
}

/*------------------------------------------------------------------------*/

#define BTOR_CHKCLONE_SLV_STATS(solver, csolver, field)   \
  do                                                      \
  {                                                       \
    assert (csolver->stats.field == solver->stats.field); \
  } while (0)

#define BTOR_CHKCLONE_SLV_STATE(solver, csolver, field) \
  do                                                    \
  {                                                     \
    assert (csolver->field == solver->field);           \
  } while (0)

static void
chkclone_slv (Btor *btor, Btor *clone)
{
  uint32_t i, h;

  h = btor_opt_get (btor, BTOR_OPT_FUN_JUST_HEURISTIC);

  assert ((!btor->slv && !clone->slv) || (btor->slv && clone->slv));
  if (!btor->slv) return;
  assert (btor->slv != clone->slv);
  assert (btor->slv->kind == clone->slv->kind);

  if (btor->slv->kind == BTOR_FUN_SOLVER_KIND)
  {
    BtorFunSolver *slv  = BTOR_FUN_SOLVER (btor);
    BtorFunSolver *cslv = BTOR_FUN_SOLVER (clone);
    BtorPtrHashTableIterator it;
    BtorPtrHashTableIterator cit;

    chkclone_node_ptr_hash_table (slv->lemmas, cslv->lemmas, 0);

    if (slv->score)
    {
      assert (cslv->score);
      assert (slv->score->size == cslv->score->size);
      assert (slv->score->count == cslv->score->count);
      assert (slv->score->hash == cslv->score->hash);
      assert (slv->score->cmp == cslv->score->cmp);
      assert (!slv->score->first || cslv->score->first);
      if (h == BTOR_JUST_HEUR_BRANCH_MIN_APP)
      {
        btor_iter_hashptr_init (&it, slv->score);
        btor_iter_hashptr_init (&cit, cslv->score);
        while (btor_iter_hashptr_has_next (&it))
        {
          assert (btor_iter_hashptr_has_next (&cit));
          chkclone_node_ptr_hash_table (
              (BtorPtrHashTable *) it.bucket->data.as_ptr,
              (BtorPtrHashTable *) cit.bucket->data.as_ptr,
              0);
          BTOR_CHKCLONE_EXPID (btor_iter_hashptr_next (&it),
                               btor_iter_hashptr_next (&cit));
        }
        assert (!btor_iter_hashptr_has_next (&cit));
      }
      else
      {
        assert (h == BTOR_JUST_HEUR_BRANCH_MIN_DEP);
        chkclone_node_ptr_hash_table (slv->score, cslv->score, cmp_data_as_int);
      }
    }
    else
    {
      assert (!cslv->score);
    }

    assert (BTOR_COUNT_STACK (slv->stats.lemmas_size)
            == BTOR_COUNT_STACK (cslv->stats.lemmas_size));
    for (i = 0; i < BTOR_COUNT_STACK (slv->stats.lemmas_size); i++)
      assert (BTOR_PEEK_STACK (slv->stats.lemmas_size, i)
              == BTOR_PEEK_STACK (cslv->stats.lemmas_size, i));

    BTOR_CHKCLONE_SLV_STATS (slv, cslv, lod_refinements);
    BTOR_CHKCLONE_SLV_STATS (slv, cslv, refinement_iterations);
    BTOR_CHKCLONE_SLV_STATS (slv, cslv, function_congruence_conflicts);
    BTOR_CHKCLONE_SLV_STATS (slv, cslv, beta_reduction_conflicts);
    BTOR_CHKCLONE_SLV_STATS (slv, cslv, extensionality_lemmas);
    BTOR_CHKCLONE_SLV_STATS (slv, cslv, lemmas_size_sum);
    BTOR_CHKCLONE_SLV_STATS (slv, cslv, dp_failed_vars);
    BTOR_CHKCLONE_SLV_STATS (slv, cslv, dp_assumed_vars);
    BTOR_CHKCLONE_SLV_STATS (slv, cslv, dp_failed_applies);
    BTOR_CHKCLONE_SLV_STATS (slv, cslv, dp_assumed_applies);
    BTOR_CHKCLONE_SLV_STATS (slv, cslv, dp_failed_eqs);
    BTOR_CHKCLONE_SLV_STATS (slv, cslv, dp_assumed_eqs);
    BTOR_CHKCLONE_SLV_STATS (slv, cslv, eval_exp_calls);
    BTOR_CHKCLONE_SLV_STATS (slv, cslv, propagations);
    BTOR_CHKCLONE_SLV_STATS (slv, cslv, propagations_down);
  }
  else if (btor->slv->kind == BTOR_SLS_SOLVER_KIND)
  {
    BtorSLSMove *m, *cm;
    BtorSLSSolver *slv  = BTOR_SLS_SOLVER (btor);
    BtorSLSSolver *cslv = BTOR_SLS_SOLVER (clone);

    chkclone_int_hash_map (slv->roots, cslv->roots, cmp_data_as_int);
    chkclone_int_hash_map (
        slv->weights, cslv->weights, cmp_data_as_sls_constr_data_ptr);
    chkclone_int_hash_map (slv->score, cslv->score, cmp_data_as_dbl);

    assert (BTOR_COUNT_STACK (slv->moves) == BTOR_COUNT_STACK (cslv->moves));
    for (i = 0; i < BTOR_COUNT_STACK (slv->moves); i++)
    {
      m = BTOR_PEEK_STACK (slv->moves, i);
      assert (m);
      cm = BTOR_PEEK_STACK (cslv->moves, i);
      assert (cm);
      assert (m->sc == cm->sc);
      chkclone_int_hash_map (m->cans, cm->cans, cmp_data_as_bv_ptr);
    }

    BTOR_CHKCLONE_SLV_STATE (slv, cslv, npropmoves);
    BTOR_CHKCLONE_SLV_STATE (slv, cslv, nslsmoves);
    BTOR_CHKCLONE_SLV_STATE (slv, cslv, sum_score);
    BTOR_CHKCLONE_SLV_STATE (slv, cslv, prop_flip_cond_const_prob);
    BTOR_CHKCLONE_SLV_STATE (slv, cslv, prop_flip_cond_const_prob_delta);
    BTOR_CHKCLONE_SLV_STATE (slv, cslv, prop_nflip_cond_const);

    chkclone_int_hash_map (slv->max_cans, cslv->max_cans, cmp_data_as_bv_ptr);

    BTOR_CHKCLONE_SLV_STATE (slv, cslv, max_score);
    BTOR_CHKCLONE_SLV_STATE (slv, cslv, max_move);
    BTOR_CHKCLONE_SLV_STATE (slv, cslv, max_gw);

    BTOR_CHKCLONE_SLV_STATS (slv, cslv, restarts);
    BTOR_CHKCLONE_SLV_STATS (slv, cslv, moves);
    BTOR_CHKCLONE_SLV_STATS (slv, cslv, flips);
    BTOR_CHKCLONE_SLV_STATS (slv, cslv, move_flip);
    BTOR_CHKCLONE_SLV_STATS (slv, cslv, move_inc);
    BTOR_CHKCLONE_SLV_STATS (slv, cslv, move_dec);
    BTOR_CHKCLONE_SLV_STATS (slv, cslv, move_not);
    BTOR_CHKCLONE_SLV_STATS (slv, cslv, move_range);
    BTOR_CHKCLONE_SLV_STATS (slv, cslv, move_seg);
    BTOR_CHKCLONE_SLV_STATS (slv, cslv, move_rand);
    BTOR_CHKCLONE_SLV_STATS (slv, cslv, move_rand_walk);
    BTOR_CHKCLONE_SLV_STATS (slv, cslv, move_prop);
    BTOR_CHKCLONE_SLV_STATS (slv, cslv, move_prop_rec_conf);
    BTOR_CHKCLONE_SLV_STATS (slv, cslv, move_prop_non_rec_conf);
    BTOR_CHKCLONE_SLV_STATS (slv, cslv, move_gw_flip);
    BTOR_CHKCLONE_SLV_STATS (slv, cslv, move_gw_inc);
    BTOR_CHKCLONE_SLV_STATS (slv, cslv, move_gw_dec);
    BTOR_CHKCLONE_SLV_STATS (slv, cslv, move_gw_not);
    BTOR_CHKCLONE_SLV_STATS (slv, cslv, move_gw_range);
    BTOR_CHKCLONE_SLV_STATS (slv, cslv, move_gw_seg);
    BTOR_CHKCLONE_SLV_STATS (slv, cslv, move_gw_rand);
    BTOR_CHKCLONE_SLV_STATS (slv, cslv, move_gw_rand_walk);
    BTOR_CHKCLONE_SLV_STATS (slv, cslv, updates);
  }
  else if (btor->slv->kind == BTOR_PROP_SOLVER_KIND)
  {
    BtorPropSolver *slv  = BTOR_PROP_SOLVER (btor);
    BtorPropSolver *cslv = BTOR_PROP_SOLVER (clone);

    chkclone_int_hash_map (slv->roots, cslv->roots, cmp_data_as_int);
    chkclone_int_hash_map (slv->score, cslv->score, cmp_data_as_dbl);

    BTOR_CHKCLONE_SLV_STATE (slv, cslv, flip_cond_const_prob);
    BTOR_CHKCLONE_SLV_STATE (slv, cslv, flip_cond_const_prob_delta);
    BTOR_CHKCLONE_SLV_STATE (slv, cslv, nflip_cond_const);

    BTOR_CHKCLONE_SLV_STATS (slv, cslv, restarts);
    BTOR_CHKCLONE_SLV_STATS (slv, cslv, moves);
    BTOR_CHKCLONE_SLV_STATS (slv, cslv, rec_conf);
    BTOR_CHKCLONE_SLV_STATS (slv, cslv, non_rec_conf);
    BTOR_CHKCLONE_SLV_STATS (slv, cslv, props);
    BTOR_CHKCLONE_SLV_STATS (slv, cslv, props_inv);
    BTOR_CHKCLONE_SLV_STATS (slv, cslv, props_cons);
    BTOR_CHKCLONE_SLV_STATS (slv, cslv, updates);
#ifndef NDEBUG
    BTOR_CHKCLONE_SLV_STATS (slv, cslv, inv_add);
    BTOR_CHKCLONE_SLV_STATS (slv, cslv, inv_and);
    BTOR_CHKCLONE_SLV_STATS (slv, cslv, inv_eq);
    BTOR_CHKCLONE_SLV_STATS (slv, cslv, inv_ult);
    BTOR_CHKCLONE_SLV_STATS (slv, cslv, inv_sll);
    BTOR_CHKCLONE_SLV_STATS (slv, cslv, inv_srl);
    BTOR_CHKCLONE_SLV_STATS (slv, cslv, inv_mul);
    BTOR_CHKCLONE_SLV_STATS (slv, cslv, inv_udiv);
    BTOR_CHKCLONE_SLV_STATS (slv, cslv, inv_urem);
    BTOR_CHKCLONE_SLV_STATS (slv, cslv, inv_concat);
    BTOR_CHKCLONE_SLV_STATS (slv, cslv, inv_slice);

    BTOR_CHKCLONE_SLV_STATS (slv, cslv, cons_add);
    BTOR_CHKCLONE_SLV_STATS (slv, cslv, cons_and);
    BTOR_CHKCLONE_SLV_STATS (slv, cslv, cons_eq);
    BTOR_CHKCLONE_SLV_STATS (slv, cslv, cons_ult);
    BTOR_CHKCLONE_SLV_STATS (slv, cslv, cons_sll);
    BTOR_CHKCLONE_SLV_STATS (slv, cslv, cons_srl);
    BTOR_CHKCLONE_SLV_STATS (slv, cslv, cons_mul);
    BTOR_CHKCLONE_SLV_STATS (slv, cslv, cons_udiv);
    BTOR_CHKCLONE_SLV_STATS (slv, cslv, cons_urem);
    BTOR_CHKCLONE_SLV_STATS (slv, cslv, cons_concat);
    BTOR_CHKCLONE_SLV_STATS (slv, cslv, cons_slice);
#endif
  }
  else if (btor->slv->kind == BTOR_AIGPROP_SOLVER_KIND)
  {
    BtorAIGPropSolver *slv  = BTOR_AIGPROP_SOLVER (btor);
    BtorAIGPropSolver *cslv = BTOR_AIGPROP_SOLVER (clone);

    assert (slv->aprop != cslv->aprop);
    assert (slv->aprop->roots == cslv->aprop->roots);

    chkclone_int_hash_map (
        slv->aprop->unsatroots, cslv->aprop->unsatroots, cmp_data_as_int);
    chkclone_int_hash_map (
        slv->aprop->model, cslv->aprop->model, cmp_data_as_int);
    chkclone_int_hash_map (
        slv->aprop->score, cslv->aprop->score, cmp_data_as_dbl);

    BTOR_CHKCLONE_SLV_STATE (slv->aprop, cslv->aprop, loglevel);
    BTOR_CHKCLONE_SLV_STATE (slv->aprop, cslv->aprop, seed);
    BTOR_CHKCLONE_SLV_STATE (slv->aprop, cslv->aprop, use_restarts);
    BTOR_CHKCLONE_SLV_STATE (slv->aprop, cslv->aprop, use_bandit);

    BTOR_CHKCLONE_SLV_STATS (slv, cslv, moves);
    BTOR_CHKCLONE_SLV_STATS (slv, cslv, restarts);
  }
}

/*------------------------------------------------------------------------*/

void
btor_chkclone (Btor *btor, Btor *clone)
{
  assert (btor);
  assert (clone);
  assert (btor != clone);

#ifdef BTOR_USE_LINGELING
  if (btor_opt_get (btor, BTOR_OPT_SAT_ENGINE) != BTOR_SAT_ENGINE_LINGELING)
    return;
#else
  return;
#endif

  chkclone_mem (btor, clone);
  chkclone_state (btor, clone);
  chkclone_stats (btor, clone);

  chkclone_opts (btor, clone);

  chkclone_assignment_lists (btor, clone);

  assert ((!btor->avmgr && !clone->avmgr) || (btor->avmgr && clone->avmgr));

  if (btor->avmgr)
  {
    chkclone_aig_unique_table (btor, clone);
    chkclone_aig_id_table (btor, clone);
    chkclone_aig_cnf_id_table (btor, clone);
  }

  chkclone_node_id_table (btor, clone);
  chkclone_node_unique_table (btor, clone);

  chkclone_node_ptr_stack (&btor->functions_with_model,
                           &clone->functions_with_model);

  chkclone_tables (btor, clone);

  chkclone_slv (btor, clone);
}

/*------------------------------------------------------------------------*/
#endif
/*------------------------------------------------------------------------*/
