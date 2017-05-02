/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2013 Armin Biere.
 *  Copyright (C) 2012-2016 Mathias Preiner.
 *  Copyright (C) 2012-2017 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef NDEBUG
#include "btordbg.h"
#include "utils/btorhashptr.h"

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
    static_rho = btor_lambda_get_static_rho (cur);
    if (!static_rho) continue;

    btor_iter_hashptr_init (&iit, static_rho);
    while (btor_iter_hashptr_has_next (&iit))
    {
      data = iit.bucket->data.as_ptr;
      key  = btor_iter_hashptr_next (&iit);
      assert (data);
      if (btor_is_proxy_node (data)) return false;
      if (btor_is_proxy_node (key)) return false;
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
        if (btor_is_proxy_node (cur->e[j])) return false;
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
    if (btor_is_proxy_node (cur)) return false;
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
    if (BTOR_REAL_ADDR_NODE (btor_iter_hashptr_next (&it))->simplified)
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
    if (btor_is_bv_const_node (cur)) return false;
  }

  btor_iter_hashptr_init (&it, btor->synthesized_constraints);
  while (btor_iter_hashptr_has_next (&it))
  {
    cur = btor_iter_hashptr_next (&it);
    assert (cur);
    if (btor_is_bv_const_node (cur)) return false;
  }
  return true;
}

bool
btor_dbg_check_assumptions_simp_free (const Btor *btor)
{
  BtorPtrHashTableIterator it;
  btor_iter_hashptr_init (&it, btor->assumptions);
  while (btor_iter_hashptr_has_next (&it))
    if (BTOR_REAL_ADDR_NODE (btor_iter_hashptr_next (&it))->simplified)
      return false;
  return true;
}

#endif
