/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2013 Armin Biere.
 *  Copyright (C) 2012-2015 Mathias Preiner.
 *  Copyright (C) 2012-2014 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef NDEBUG
#include "btordbg.h"
#include "utils/btoriter.h"

int
check_lambdas_static_rho_proxy_free_dbg (const Btor *btor)
{
  BtorNode *cur, *data, *key;
  BtorHashTableIterator it, iit;
  BtorPtrHashTable *static_rho;

  init_node_hash_table_iterator (&it, btor->lambdas);
  while (has_next_node_hash_table_iterator (&it))
  {
    cur        = next_node_hash_table_iterator (&it);
    static_rho = btor_lambda_get_static_rho (cur);
    if (!static_rho) continue;

    init_node_hash_table_iterator (&iit, static_rho);
    while (has_next_node_hash_table_iterator (&iit))
    {
      data = iit.bucket->data.asPtr;
      key  = next_node_hash_table_iterator (&iit);
      assert (data);
      if (BTOR_IS_PROXY_NODE (BTOR_REAL_ADDR_NODE (data))) return 0;
      if (BTOR_IS_PROXY_NODE (BTOR_REAL_ADDR_NODE (key))) return 0;
    }
  }
  return 1;
}

int
check_unique_table_children_proxy_free_dbg (const Btor *btor)
{
  int i, j;
  BtorNode *cur;

  for (i = 0; i < btor->nodes_unique_table.size; i++)
    for (cur = btor->nodes_unique_table.chains[i]; cur; cur = cur->next)
      for (j = 0; j < cur->arity; j++)
        if (BTOR_IS_PROXY_NODE (BTOR_REAL_ADDR_NODE (cur->e[j]))) return 0;
  return 1;
}

int
check_id_table_mark_unset_dbg (const Btor *btor)
{
  int i;
  BtorNode *cur;

  for (i = 1; i < BTOR_COUNT_STACK (btor->nodes_id_table); i++)
  {
    cur = BTOR_PEEK_STACK (btor->nodes_id_table, i);
    if (!cur) continue;
    if (cur->mark != 0) return 0;
  }
  return 1;
}

int
check_id_table_aux_mark_unset_dbg (const Btor *btor)
{
  int i;
  BtorNode *cur;

  for (i = 1; i < BTOR_COUNT_STACK (btor->nodes_id_table); i++)
  {
    cur = BTOR_PEEK_STACK (btor->nodes_id_table, i);
    if (!cur) continue;
    if (cur->aux_mark != 0) return 0;
  }
  return 1;
}

int
check_unique_table_merge_unset_dbg (const Btor *btor)
{
  int i;
  BtorNode *cur;

  for (i = 0; i < btor->nodes_unique_table.size; i++)
    for (cur = btor->nodes_unique_table.chains[i]; cur; cur = cur->next)
      if (cur->merge != 0) return 0;
  return 1;
}

int
check_hash_table_proxy_free_dbg (BtorPtrHashTable *table)
{
  BtorHashTableIterator it;
  BtorNode *cur;

  init_node_hash_table_iterator (&it, table);
  while (has_next_node_hash_table_iterator (&it))
  {
    cur = next_node_hash_table_iterator (&it);
    if (BTOR_IS_PROXY_NODE (BTOR_REAL_ADDR_NODE (cur))) return 0;
  }
  return 1;
}

int
check_all_hash_tables_proxy_free_dbg (const Btor *btor)
{
  if (!check_hash_table_proxy_free_dbg (btor->varsubst_constraints)) return 0;
  if (!check_hash_table_proxy_free_dbg (btor->embedded_constraints)) return 0;
  if (!check_hash_table_proxy_free_dbg (btor->unsynthesized_constraints))
    return 0;
  if (!check_hash_table_proxy_free_dbg (btor->synthesized_constraints))
    return 0;
  return 1;
}

int
check_hash_table_simp_free_dbg (BtorPtrHashTable *table)
{
  BtorHashTableIterator it;
  init_node_hash_table_iterator (&it, table);
  while (has_next_node_hash_table_iterator (&it))
    if (BTOR_REAL_ADDR_NODE (next_node_hash_table_iterator (&it))->simplified)
      return 0;
  return 1;
}

int
check_all_hash_tables_simp_free_dbg (const Btor *btor)
{
  if (!check_hash_table_simp_free_dbg (btor->varsubst_constraints)) return 0;
  if (!check_hash_table_simp_free_dbg (btor->embedded_constraints)) return 0;
  if (!check_hash_table_simp_free_dbg (btor->unsynthesized_constraints))
    return 0;
  if (!check_hash_table_simp_free_dbg (btor->synthesized_constraints)) return 0;
  return 1;
}

int
check_reachable_flag_dbg (const Btor *btor)
{
  int i;
  BtorNode *cur, *parent;
  BtorNodeIterator it;

  for (i = BTOR_COUNT_STACK (btor->nodes_id_table) - 1; i >= 0; i--)
  {
    if (!(cur = BTOR_PEEK_STACK (btor->nodes_id_table, i))) continue;

    init_full_parent_iterator (&it, cur);

    while (has_next_parent_full_parent_iterator (&it))
    {
      parent = next_parent_full_parent_iterator (&it);
      if (parent->reachable && !cur->reachable) return 0;
    }
  }
  return 1;
}

int
check_constraints_not_const_dbg (Btor *btor)
{
  BtorNode *cur;
  BtorHashTableIterator it;

  init_node_hash_table_iterator (&it, btor->unsynthesized_constraints);
  while (has_next_node_hash_table_iterator (&it))
  {
    cur = next_node_hash_table_iterator (&it);
    assert (cur);
    cur = BTOR_REAL_ADDR_NODE (cur);
    if (BTOR_IS_BV_CONST_NODE (cur)) return 0;
  }

  init_node_hash_table_iterator (&it, btor->synthesized_constraints);
  while (has_next_node_hash_table_iterator (&it))
  {
    cur = next_node_hash_table_iterator (&it);
    assert (cur);
    cur = BTOR_REAL_ADDR_NODE (cur);
    if (BTOR_IS_BV_CONST_NODE (cur)) return 0;
  }
  return 1;
}

#endif
