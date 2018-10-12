/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2013 Armin Biere.
 *  Copyright (C) 2012-2017 Mathias Preiner.
 *  Copyright (C) 2012-2017 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

/*------------------------------------------------------------------------*/
#ifndef NDEBUG
/*------------------------------------------------------------------------*/

#include "btordbg.h"

#include <limits.h>
#include "utils/btorhashptr.h"
#include "utils/btorutil.h"

/*------------------------------------------------------------------------*/
/* core                                                                   */
/*------------------------------------------------------------------------*/

bool
btor_dbg_check_lambdas_static_rho_proxy_free (const Btor *btor)
{
  BtorNode *cur, *data, *key;
  BtorPtrHashTableIterator it, iit;
  BtorPtrHashTable *static_rho;

  btor_iter_hashptr_init (&it, btor->lambdas);
  while (btor_iter_hashptr_has_next (&it))
  {
    cur        = btor_iter_hashptr_next (&it);
    static_rho = btor_node_lambda_get_static_rho (cur);
    if (!static_rho) continue;

    btor_iter_hashptr_init (&iit, static_rho);
    while (btor_iter_hashptr_has_next (&iit))
    {
      data = iit.bucket->data.as_ptr;
      key  = btor_iter_hashptr_next (&iit);
      assert (data);
      if (btor_node_is_proxy (data)) return false;
      if (btor_node_is_proxy (key)) return false;
    }
  }
  return true;
}

bool
btor_dbg_check_unique_table_children_proxy_free (const Btor *btor)
{
  uint32_t i, j;
  BtorNode *cur;

  for (i = 0; i < btor->nodes_unique_table.size; i++)
    for (cur = btor->nodes_unique_table.chains[i]; cur; cur = cur->next)
      for (j = 0; j < cur->arity; j++)
        if (btor_node_is_proxy (cur->e[j])) return false;
  return true;
}

bool
btor_dbg_check_hash_table_proxy_free (BtorPtrHashTable *table)
{
  BtorPtrHashTableIterator it;
  BtorNode *cur;

  btor_iter_hashptr_init (&it, table);
  while (btor_iter_hashptr_has_next (&it))
  {
    cur = btor_iter_hashptr_next (&it);
    if (btor_node_is_proxy (cur)) return false;
  }
  return true;
}

bool
btor_dbg_check_all_hash_tables_proxy_free (const Btor *btor)
{
  if (!btor_dbg_check_hash_table_proxy_free (btor->varsubst_constraints))
    return false;
  if (!btor_dbg_check_hash_table_proxy_free (btor->embedded_constraints))
    return false;
  if (!btor_dbg_check_hash_table_proxy_free (btor->unsynthesized_constraints))
    return false;
  if (!btor_dbg_check_hash_table_proxy_free (btor->synthesized_constraints))
    return false;
  return true;
}

bool
btor_dbg_check_hash_table_simp_free (BtorPtrHashTable *table)
{
  BtorPtrHashTableIterator it;
  btor_iter_hashptr_init (&it, table);
  while (btor_iter_hashptr_has_next (&it))
    if (btor_node_real_addr (btor_iter_hashptr_next (&it))->simplified)
      return false;
  return true;
}

bool
btor_dbg_check_all_hash_tables_simp_free (const Btor *btor)
{
  if (!btor_dbg_check_hash_table_simp_free (btor->varsubst_constraints))
    return false;
  if (!btor_dbg_check_hash_table_simp_free (btor->embedded_constraints))
    return false;
  if (!btor_dbg_check_hash_table_simp_free (btor->unsynthesized_constraints))
    return false;
  if (!btor_dbg_check_hash_table_simp_free (btor->synthesized_constraints))
    return false;
  return true;
}

bool
btor_dbg_check_constraints_not_const (const Btor *btor)
{
  BtorNode *cur;
  BtorPtrHashTableIterator it;

  btor_iter_hashptr_init (&it, btor->unsynthesized_constraints);
  while (btor_iter_hashptr_has_next (&it))
  {
    cur = btor_iter_hashptr_next (&it);
    assert (cur);
    if (btor_node_is_bv_const (cur)) return false;
  }

  btor_iter_hashptr_init (&it, btor->synthesized_constraints);
  while (btor_iter_hashptr_has_next (&it))
  {
    cur = btor_iter_hashptr_next (&it);
    assert (cur);
    if (btor_node_is_bv_const (cur)) return false;
  }
  return true;
}

bool
btor_dbg_check_assumptions_simp_free (const Btor *btor)
{
  BtorPtrHashTableIterator it;
  btor_iter_hashptr_init (&it, btor->assumptions);
  while (btor_iter_hashptr_has_next (&it))
    if (btor_node_real_addr (btor_iter_hashptr_next (&it))->simplified)
      return false;
  return true;
}

/*------------------------------------------------------------------------*/
/* exp                                                                    */
/*------------------------------------------------------------------------*/

bool
btor_dbg_precond_slice_exp (Btor *btor,
                            const BtorNode *exp,
                            uint32_t upper,
                            uint32_t lower)
{
  assert (btor);
  assert (exp);
  assert (!btor_node_real_addr (exp)->simplified);
  assert (!btor_node_is_fun (exp));
  assert (upper >= lower);
  assert (upper < btor_node_bv_get_width (btor, exp));
  assert (btor_node_real_addr (exp)->btor == btor);
  return true;
}

bool
btor_dbg_precond_ext_exp (Btor *btor, const BtorNode *exp)
{
  assert (btor_dbg_precond_regular_unary_bv_exp (btor, exp));
  return true;
}

bool
btor_dbg_precond_regular_unary_bv_exp (Btor *btor, const BtorNode *exp)
{
  assert (btor);
  assert (exp);
  assert (!btor_node_real_addr (exp)->simplified);
  assert (!btor_node_is_fun (exp));
  assert (btor_node_real_addr (exp)->btor == btor);
  return true;
}

bool
btor_dbg_precond_eq_exp (Btor *btor, const BtorNode *e0, const BtorNode *e1)
{
  BtorNode *real_e0, *real_e1;

  assert (btor);
  assert (e0);
  assert (e1);

  real_e0 = btor_node_real_addr (e0);
  real_e1 = btor_node_real_addr (e1);

  assert (real_e0);
  assert (real_e1);
  assert (real_e0->btor == btor);
  assert (real_e1->btor == btor);
  assert (!real_e0->simplified);
  assert (!real_e1->simplified);
  assert (btor_node_get_sort_id (real_e0) == btor_node_get_sort_id (real_e1));
  assert (real_e0->is_array == real_e1->is_array);
  assert (!btor_node_is_fun (real_e0)
          || (btor_node_is_regular (e0) && btor_node_is_regular (e1)));
  return true;
}

bool
btor_dbg_precond_concat_exp (Btor *btor, const BtorNode *e0, const BtorNode *e1)
{
  assert (btor);
  assert (e0);
  assert (e1);
  assert (!btor_node_real_addr (e0)->simplified);
  assert (!btor_node_real_addr (e1)->simplified);
  assert (!btor_node_is_fun (e0));
  assert (!btor_node_is_fun (e1));
  assert (btor_node_bv_get_width (btor, e0)
          <= INT32_MAX - btor_node_bv_get_width (btor, e1));
  assert (btor_node_real_addr (e0)->btor == btor);
  assert (btor_node_real_addr (e1)->btor == btor);
  return true;
}

bool
btor_dbg_precond_shift_exp (Btor *btor, const BtorNode *e0, const BtorNode *e1)
{
  assert (btor);
  assert (e0);
  assert (e1);
  assert (!btor_node_real_addr (e0)->simplified);
  assert (!btor_node_real_addr (e1)->simplified);
  assert (!btor_node_is_fun (e0));
  assert (!btor_node_is_fun (e1));
  assert (btor_node_bv_get_width (btor, e0) > 1);
  assert (btor_util_is_power_of_2 (btor_node_bv_get_width (btor, e0)));
  assert (btor_util_log_2 (btor_node_bv_get_width (btor, e0))
          == btor_node_bv_get_width (btor, e1));
  assert (btor_node_real_addr (e0)->btor == btor);
  assert (btor_node_real_addr (e1)->btor == btor);
  return true;
}

bool
btor_dbg_precond_regular_binary_bv_exp (Btor *btor,
                                        const BtorNode *e0,
                                        const BtorNode *e1)
{
  assert (btor);
  assert (e0);
  assert (e1);
  assert (!btor_node_real_addr (e0)->simplified);
  assert (!btor_node_real_addr (e1)->simplified);
  assert (!btor_node_is_fun (e0));
  assert (!btor_node_is_fun (e1));
  assert (btor_node_get_sort_id (e0) == btor_node_get_sort_id (e1));
  assert (btor_node_real_addr (e0)->btor == btor);
  assert (btor_node_real_addr (e1)->btor == btor);
  return true;
}

bool
btor_dbg_precond_read_exp (Btor *btor,
                           const BtorNode *e_array,
                           const BtorNode *e_index)
{
  assert (btor);
  assert (e_array);
  assert (e_index);
  assert (btor_node_is_regular (e_array));
  assert (btor_node_is_fun (e_array));
  assert (!e_array->simplified);
  assert (!btor_node_real_addr (e_index)->simplified);
  assert (!btor_node_is_fun (e_index));
  assert (btor_sort_array_get_index (btor, btor_node_get_sort_id (e_array))
          == btor_node_get_sort_id (e_index));
  assert (btor_node_real_addr (e_array)->btor == btor);
  assert (btor_node_real_addr (e_index)->btor == btor);
  assert (e_array->is_array);
  return true;
}

bool
btor_dbg_precond_write_exp (Btor *btor,
                            const BtorNode *e_array,
                            const BtorNode *e_index,
                            const BtorNode *e_value)
{
  assert (btor);
  assert (e_array);
  assert (e_index);
  assert (e_value);
  assert (btor_node_is_regular (e_array));
  assert (btor_node_is_fun (e_array));
  assert (!e_array->simplified);
  assert (!btor_node_real_addr (e_index)->simplified);
  assert (!btor_node_real_addr (e_value)->simplified);
  assert (!btor_node_is_fun (e_index));
  assert (!btor_node_is_fun (e_value));
  assert (btor_sort_array_get_index (btor, btor_node_get_sort_id (e_array))
          == btor_node_get_sort_id (e_index));
  assert (btor_sort_array_get_element (btor, btor_node_get_sort_id (e_array))
          == btor_node_get_sort_id (e_value));
  assert (btor_node_real_addr (e_array)->btor == btor);
  assert (btor_node_real_addr (e_index)->btor == btor);
  assert (btor_node_real_addr (e_value)->btor == btor);
  assert (e_array->is_array);
  return true;
}

bool
btor_dbg_precond_cond_exp (Btor *btor,
                           const BtorNode *e_cond,
                           const BtorNode *e_if,
                           const BtorNode *e_else)
{
  assert (btor);
  assert (e_cond);
  assert (e_if);
  assert (e_else);
  assert (!btor_node_real_addr (e_cond)->simplified);
  assert (btor_node_bv_get_width (btor, e_cond) == 1);

  BtorNode *real_e_if, *real_e_else;

  real_e_if   = btor_node_real_addr (e_if);
  real_e_else = btor_node_real_addr (e_else);

  assert (!real_e_if->simplified);
  assert (!real_e_else->simplified);
  assert (btor_node_get_sort_id (real_e_if)
          == btor_node_get_sort_id (real_e_else));
  assert (btor_node_real_addr (e_cond)->btor == btor);
  assert (real_e_if->btor == btor);
  assert (real_e_else->btor == btor);
  assert (real_e_if->is_array == real_e_else->is_array);
  return true;
}

bool
btor_dbg_precond_apply_exp (Btor *btor,
                            const BtorNode *fun,
                            const BtorNode *args)
{
  assert (btor);
  assert (fun);
  assert (args);
  assert (btor_node_is_regular (fun));
  assert (btor_node_is_regular (args));
  assert (btor_node_is_fun (fun));
  assert (btor_node_is_args (args));
  assert (btor_sort_fun_get_domain (btor, btor_node_get_sort_id (fun))
          == btor_node_get_sort_id (args));
  return true;
}

/*------------------------------------------------------------------------*/
#endif
/*------------------------------------------------------------------------*/
