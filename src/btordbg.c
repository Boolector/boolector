/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2013 Armin Biere.
 *  Copyright (C) 2012-2015 Mathias Preiner.
 *  Copyright (C) 2012-2016 Aina Niemetz.
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
btor_check_lambdas_static_rho_proxy_free_dbg (const Btor *btor)
{
  BtorNode *cur, *data, *key;
  BtorPtrHashTableIterator it, iit;
  BtorPtrHashTable *static_rho;

  btor_init_ptr_hash_table_iterator (&it, btor->lambdas);
  while (btor_has_next_ptr_hash_table_iterator (&it))
  {
    cur        = btor_next_ptr_hash_table_iterator (&it);
    static_rho = btor_lambda_get_static_rho (cur);
    if (!static_rho) continue;

    btor_init_ptr_hash_table_iterator (&iit, static_rho);
    while (btor_has_next_ptr_hash_table_iterator (&iit))
    {
      data = iit.bucket->data.as_ptr;
      key  = btor_next_ptr_hash_table_iterator (&iit);
      assert (data);
      if (btor_is_proxy_node (data)) return false;
      if (btor_is_proxy_node (key)) return false;
    }
  }
  return true;
}

bool
btor_check_unique_table_children_proxy_free_dbg (const Btor *btor)
{
  int i, j;
  BtorNode *cur;

  for (i = 0; i < btor->nodes_unique_table.size; i++)
    for (cur = btor->nodes_unique_table.chains[i]; cur; cur = cur->next)
      for (j = 0; j < cur->arity; j++)
        if (btor_is_proxy_node (cur->e[j])) return false;
  return true;
}

bool
btor_check_hash_table_proxy_free_dbg (BtorPtrHashTable *table)
{
  BtorPtrHashTableIterator it;
  BtorNode *cur;

  btor_init_ptr_hash_table_iterator (&it, table);
  while (btor_has_next_ptr_hash_table_iterator (&it))
  {
    cur = btor_next_ptr_hash_table_iterator (&it);
    if (btor_is_proxy_node (cur)) return false;
  }
  return true;
}

bool
btor_check_all_hash_tables_proxy_free_dbg (const Btor *btor)
{
  if (!btor_check_hash_table_proxy_free_dbg (btor->varsubst_constraints))
    return false;
  if (!btor_check_hash_table_proxy_free_dbg (btor->embedded_constraints))
    return false;
  if (!btor_check_hash_table_proxy_free_dbg (btor->unsynthesized_constraints))
    return false;
  if (!btor_check_hash_table_proxy_free_dbg (btor->synthesized_constraints))
    return false;
  return true;
}

bool
btor_check_hash_table_simp_free_dbg (BtorPtrHashTable *table)
{
  BtorPtrHashTableIterator it;
  btor_init_ptr_hash_table_iterator (&it, table);
  while (btor_has_next_ptr_hash_table_iterator (&it))
    if (BTOR_REAL_ADDR_NODE (btor_next_ptr_hash_table_iterator (&it))
            ->simplified)
      return false;
  return true;
}

bool
btor_check_all_hash_tables_simp_free_dbg (const Btor *btor)
{
  if (!btor_check_hash_table_simp_free_dbg (btor->varsubst_constraints))
    return false;
  if (!btor_check_hash_table_simp_free_dbg (btor->embedded_constraints))
    return false;
  if (!btor_check_hash_table_simp_free_dbg (btor->unsynthesized_constraints))
    return false;
  if (!btor_check_hash_table_simp_free_dbg (btor->synthesized_constraints))
    return false;
  return true;
}

bool
btor_check_constraints_not_const_dbg (const Btor *btor)
{
  BtorNode *cur;
  BtorPtrHashTableIterator it;

  btor_init_ptr_hash_table_iterator (&it, btor->unsynthesized_constraints);
  while (btor_has_next_ptr_hash_table_iterator (&it))
  {
    cur = btor_next_ptr_hash_table_iterator (&it);
    assert (cur);
    if (btor_is_bv_const_node (cur)) return false;
  }

  btor_init_ptr_hash_table_iterator (&it, btor->synthesized_constraints);
  while (btor_has_next_ptr_hash_table_iterator (&it))
  {
    cur = btor_next_ptr_hash_table_iterator (&it);
    assert (cur);
    if (btor_is_bv_const_node (cur)) return false;
  }
  return true;
}

bool
btor_check_assumptions_simp_free_dbg (const Btor *btor)
{
  BtorPtrHashTableIterator it;
  btor_init_ptr_hash_table_iterator (&it, btor->assumptions);
  while (btor_has_next_ptr_hash_table_iterator (&it))
    if (BTOR_REAL_ADDR_NODE (btor_next_ptr_hash_table_iterator (&it))
            ->simplified)
      return false;
  return true;
}

#endif
