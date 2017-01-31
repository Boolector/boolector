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
#include "utils/btorexpiter.h"
#include "utils/btorhashint.h"

BtorNode *
btor_skolemize_node (Btor *btor,
                     BtorNode *root,
                     BtorIntHashTable *node_map,
                     BtorPtrHashTable *skolem_consts)
{
  int32_t i;
  uint32_t j;
  char *symbol, *buf;
  size_t len;
  BtorNode *cur, *real_cur, *result, *quant, *param, *uf, **e;
  BtorNodePtrStack visit, quants, args, params;
  BtorMemMgr *mm;
  BtorIntHashTable *map;
  BtorHashTableData *d, *d_p;
  BtorSortIdStack sorts;
  BtorSortId tuple_s, fun_s;

  mm  = btor->mm;
  map = btor_new_int_hash_map (mm);

  BTOR_INIT_STACK (mm, args);
  BTOR_INIT_STACK (mm, params);
  BTOR_INIT_STACK (mm, quants);
  BTOR_INIT_STACK (mm, sorts);
  BTOR_INIT_STACK (mm, visit);
  BTOR_PUSH_STACK (visit, root);

  while (!BTOR_EMPTY_STACK (visit))
  {
    cur      = BTOR_POP_STACK (visit);
    real_cur = BTOR_REAL_ADDR_NODE (cur);
    //      assert (!BTOR_IS_QUANTIFIER_NODE (real_cur) ||
    //      !BTOR_IS_INVERTED_NODE (cur));

    d = btor_get_int_hash_map (map, real_cur->id);

    if (!d)
    {
      btor_add_int_hash_map (map, real_cur->id);

      if (btor_is_forall_node (real_cur)) BTOR_PUSH_STACK (quants, cur);

      BTOR_PUSH_STACK (visit, cur);
      for (i = real_cur->arity - 1; i >= 0; i--)
        BTOR_PUSH_STACK (visit, real_cur->e[i]);
    }
    else if (!d->as_ptr)
    {
      assert (BTOR_COUNT_STACK (args) >= real_cur->arity);
      args.top -= real_cur->arity;
      e = args.top;

      if (real_cur->arity == 0)
      {
        if (btor_is_param_node (real_cur))
        {
          symbol = btor_get_symbol_exp (btor, real_cur);
          buf    = 0;
          if (btor_param_is_exists_var (real_cur))
          {
            if (symbol)
            {
              len = strlen (symbol) + 5;
              buf = btor_malloc (mm, len);
              sprintf (buf, "sk(%s)", symbol);
            }

            /* substitute param with skolem function */
            if (BTOR_COUNT_STACK (quants) > 0)
            {
              for (i = 0; i < BTOR_COUNT_STACK (quants); i++)
              {
                quant = BTOR_PEEK_STACK (quants, i);
                d_p   = btor_get_int_hash_map (map, quant->e[0]->id);
                assert (d_p);
                assert (d_p->as_ptr);
                param = d_p->as_ptr;
                BTOR_PUSH_STACK (params, param);
                BTOR_PUSH_STACK (sorts, param->sort_id);
              }

              tuple_s =
                  btor_tuple_sort (btor, sorts.start, BTOR_COUNT_STACK (sorts));
              fun_s = btor_fun_sort (btor, tuple_s, real_cur->sort_id);
              btor_release_sort (btor, tuple_s);

              uf = btor_uf_exp (btor, fun_s, buf);
              btor_release_sort (btor, fun_s);

              result = btor_apply_exps (
                  btor, params.start, BTOR_COUNT_STACK (params), uf);

              if (skolem_consts)
                btor_add_ptr_hash_table (skolem_consts,
                                         btor_copy_exp (btor, uf));

              btor_release_exp (btor, uf);
              BTOR_RESET_STACK (sorts);
              BTOR_RESET_STACK (params);
            }
            /* substitute param with variable in outermost scope */
            else
            {
              result =
                  btor_var_exp (btor, btor_get_exp_width (btor, real_cur), buf);
              if (skolem_consts)
                btor_add_ptr_hash_table (skolem_consts,
                                         btor_copy_exp (btor, result));
            }
          }
          else
          {
            if (symbol)
            {
              len = strlen (symbol) + 3;
              buf = btor_malloc (mm, len);
              sprintf (buf, "%s!0", symbol);
            }
            result =
                btor_param_exp (btor, btor_get_exp_width (btor, real_cur), buf);
          }

          if (buf) btor_freestr (mm, buf);
        }
        else
          result = btor_copy_exp (btor, real_cur);
      }
      else if (btor_is_slice_node (real_cur))
      {
        result = btor_slice_exp (btor,
                                 e[0],
                                 btor_slice_get_upper (real_cur),
                                 btor_slice_get_lower (real_cur));
      }
      else if (btor_is_exists_node (real_cur))
      {
        assert (!btor_is_param_node (e[0]));
        result = btor_copy_exp (btor, e[1]);
      }
      else
        result = btor_create_exp (btor, real_cur->kind, e, real_cur->arity);

      for (i = 0; i < real_cur->arity; i++) btor_release_exp (btor, e[i]);

      d->as_ptr = btor_copy_exp (btor, result);
      if (node_map)
      {
        assert (!btor_contains_int_hash_map (node_map, real_cur->id));
        btor_add_int_hash_map (node_map, real_cur->id)->as_int =
            BTOR_REAL_ADDR_NODE (result)->id;
      }
    PUSH_RESULT:

      if (btor_is_forall_node (real_cur))
      {
        quant = BTOR_POP_STACK (quants);
        assert (quant == cur);
      }

      result = BTOR_COND_INVERT_NODE (cur, result);
      assert (!btor_is_quantifier_node (result)
              || !BTOR_IS_INVERTED_NODE (result));
      BTOR_PUSH_STACK (args, result);
    }
    else
    {
      assert (d->as_ptr);
      result = btor_copy_exp (btor, d->as_ptr);
      goto PUSH_RESULT;
    }
  }
  assert (BTOR_COUNT_STACK (args) == 1);
  result = BTOR_POP_STACK (args);

  for (j = 0; j < map->size; j++)
  {
    if (!map->data[j].as_ptr) continue;
    btor_release_exp (btor, map->data[j].as_ptr);
  }
  btor_delete_int_hash_map (map);
  BTOR_RELEASE_STACK (visit);
  BTOR_RELEASE_STACK (quants);
  BTOR_RELEASE_STACK (params);
  BTOR_RELEASE_STACK (args);
  BTOR_RELEASE_STACK (sorts);
  return result;
}

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
  BtorPtrHashTableIterator it;
  BtorNodePtrStack visit, quants, args;
  BtorMemMgr *mm;
  BtorIntHashTable *cache;
  BtorHashTableData *d;
  BtorNodeMap *map;
  BtorSortIdStack sorts;
  BtorSortId tuple_s, fun_s;
  BtorNodeMapIterator nit;

  mm    = btor->mm;
  cache = btor_new_int_hash_map (mm);
  map   = btor_new_node_map (btor);

  BTOR_INIT_STACK (mm, visit);

  /* push roots */
  btor_init_ptr_hash_table_iterator (&it, btor->unsynthesized_constraints);
  while (btor_has_next_ptr_hash_table_iterator (&it))
  {
    cur = btor_next_ptr_hash_table_iterator (&it);
    BTOR_PUSH_STACK (visit, cur);
  }

  btor_init_substitutions (btor);
  BTOR_INIT_STACK (mm, quants);
  BTOR_INIT_STACK (mm, args);
  BTOR_INIT_STACK (mm, sorts);
  while (!BTOR_EMPTY_STACK (visit))
  {
    cur = BTOR_REAL_ADDR_NODE (BTOR_POP_STACK (visit));
    d   = btor_get_int_hash_map (cache, cur->id);

    if (!d)
    {
      (void) btor_add_int_hash_map (cache, cur->id);

      if (btor_is_forall_node (cur)) BTOR_PUSH_STACK (quants, cur);

      BTOR_PUSH_STACK (visit, cur);
      for (i = 0; i < cur->arity; i++) BTOR_PUSH_STACK (visit, cur->e[i]);
    }
    else if (d->as_int == 0)
    {
      d->as_int = 1;

      if (btor_is_forall_node (cur))
      {
        quant = BTOR_POP_STACK (quants);
        assert (quant == cur);
      }
      else if (btor_is_exists_node (cur) && BTOR_COUNT_STACK (quants) > 0)
      {
        param = cur->e[0];
        for (i = 0; i < BTOR_COUNT_STACK (quants); i++)
        {
          quant = BTOR_PEEK_STACK (quants, i);
          BTOR_PUSH_STACK (args, quant->e[0]);
          BTOR_PUSH_STACK (sorts, quant->e[0]->sort_id);
        }

        tuple_s = btor_tuple_sort (btor, sorts.start, BTOR_COUNT_STACK (sorts));
        fun_s   = btor_fun_sort (btor, tuple_s, param->sort_id);

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
        app = btor_apply_exps (btor, args.start, BTOR_COUNT_STACK (args), uf);
        //	      printf ("%s -> %s\n", node2string (param), node2string
        //(uf));

        btor_map_node (map, param, app);
        btor_freestr (mm, buf);
        btor_release_sort (btor, tuple_s);
        btor_release_sort (btor, fun_s);
        btor_release_exp (btor, uf);
        BTOR_RESET_STACK (sorts);
        BTOR_RESET_STACK (args);
      }
    }
  }

  btor_init_ptr_hash_table_iterator (&it, btor->quantifiers);
  while (btor_has_next_ptr_hash_table_iterator (&it))
  {
    cur = btor_next_ptr_hash_table_iterator (&it);

    if (btor_is_forall_node (cur)) continue;

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
  BTOR_RELEASE_STACK (visit);
  BTOR_RELEASE_STACK (quants);
  BTOR_RELEASE_STACK (args);
  BTOR_RELEASE_STACK (sorts);
}
