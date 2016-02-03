/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2016 Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "normalizer/btorskolemize.h"
#include "btorcore.h"
#include "utils/btorhashint.h"
#include "utils/btoriter.h"

void
btor_skolemize (Btor *btor)
{
  assert (btor->synthesized_constraints->count == 0);
  assert (btor->embedded_constraints->count == 0);
  assert (btor->varsubst_constraints->count == 0);

  int i;
  char *symbol, *buf;
  size_t len;
  BtorNode *cur, *quant, *param, *uf, *app, *subst;
  BtorHashTableIterator it;
  BtorNodePtrStack visit, quants, args;
  BtorMemMgr *mm;
  BtorIntHashTable *cache;
  BtorIntHashTableData *d;
  BtorNodeMap *map;
  BtorSortIdStack sorts;
  BtorSortId tuple_s, fun_s;
  BtorSortUniqueTable *suniq;
  BtorNodeMapIterator nit;

  mm    = btor->mm;
  suniq = &btor->sorts_unique_table;
  cache = btor_new_int_hash_map (mm);
  map   = btor_new_node_map (btor);

  BTOR_INIT_STACK (visit);

  /* push roots */
  btor_init_node_hash_table_iterator (&it, btor->unsynthesized_constraints);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    cur = btor_next_node_hash_table_iterator (&it);
    BTOR_PUSH_STACK (mm, visit, cur);
  }

  btor_init_substitutions (btor);
  BTOR_INIT_STACK (quants);
  BTOR_INIT_STACK (args);
  BTOR_INIT_STACK (sorts);
  while (!BTOR_EMPTY_STACK (visit))
  {
    cur = BTOR_REAL_ADDR_NODE (BTOR_POP_STACK (visit));
    d   = btor_get_int_hash_map (cache, cur->id);

    if (!d)
    {
      (void) btor_add_int_hash_map (cache, cur->id);

      if (BTOR_IS_FORALL_NODE (cur)) BTOR_PUSH_STACK (mm, quants, cur);

      BTOR_PUSH_STACK (mm, visit, cur);
      for (i = 0; i < cur->arity; i++) BTOR_PUSH_STACK (mm, visit, cur->e[i]);
    }
    else if (d->as_int == 0)
    {
      d->as_int = 1;

      if (BTOR_IS_FORALL_NODE (cur))
      {
        quant = BTOR_POP_STACK (quants);
        assert (quant == cur);
      }
      else if (BTOR_IS_EXISTS_NODE (cur) && BTOR_COUNT_STACK (quants) > 0)
      {
        param = cur->e[0];
        for (i = 0; i < BTOR_COUNT_STACK (quants); i++)
        {
          quant = BTOR_PEEK_STACK (quants, i);
          BTOR_PUSH_STACK (mm, args, quant->e[0]);
          BTOR_PUSH_STACK (mm, sorts, quant->e[0]->sort_id);
        }

        tuple_s =
            btor_tuple_sort (suniq, sorts.start, BTOR_COUNT_STACK (sorts));
        fun_s = btor_fun_sort (suniq, tuple_s, param->sort_id);

        symbol = btor_get_symbol_exp (btor, param);
        //	      printf ("%s\n", symbol);
        if (symbol)
        {
          len = strlen (symbol) + 5;
          buf = btor_malloc (mm, len);
          sprintf (buf, "sk(%s)", symbol);
        }
        else
          buf = 0;
        uf  = btor_uf_exp (btor, fun_s, buf);
        app = btor_apply_exps (btor, BTOR_COUNT_STACK (args), args.start, uf);
        //	      printf ("%s -> %s\n", node2string (param), node2string
        //(uf));

        btor_map_node (map, param, app);
        btor_freestr (mm, buf);
        btor_release_sort (suniq, tuple_s);
        btor_release_sort (suniq, fun_s);
        btor_release_exp (btor, uf);
        BTOR_RESET_STACK (sorts);
        BTOR_RESET_STACK (args);
      }
    }
  }

  btor_init_node_hash_table_iterator (&it, btor->quantifiers);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    cur = btor_next_node_hash_table_iterator (&it);

    if (BTOR_IS_FORALL_NODE (cur)) continue;

    /* exists quanftifier in most outer scope */
    if (!btor_mapped_node (map, cur->e[0])) continue;

    subst = btor_substitute_terms (btor, btor_binder_get_body (cur), map);
    btor_map_node (map, cur, subst);
    assert (!btor_get_ptr_hash_table (btor->substitutions, cur));
    btor_insert_substitution (btor, cur, subst, 0);
  }

  btor_substitute_and_rebuild (btor, btor->substitutions);
  btor_delete_substitutions (btor);

  btor_init_node_map_iterator (&nit, map);
  while (btor_has_next_node_map_iterator (&nit))
  {
    cur = btor_next_data_node_map_iterator (&nit)->as_ptr;
    btor_release_exp (btor, cur);
  }

  btor_delete_node_map (map);
  btor_delete_int_hash_map (cache);
  BTOR_RELEASE_STACK (mm, visit);
  BTOR_RELEASE_STACK (mm, quants);
  BTOR_RELEASE_STACK (mm, args);
  BTOR_RELEASE_STACK (mm, sorts);
}
