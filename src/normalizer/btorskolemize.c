/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2016-2017 Mathias Preiner.
 *  Copyright (C) 2017 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "normalizer/btorskolemize.h"
#include "btorcore.h"
#include "btorexp.h"
#include "btornode.h"
#include "utils/btorhashint.h"
#include "utils/btornodeiter.h"

BtorNode *
btor_skolemize_node (Btor *btor,
                     BtorNode *root,
                     BtorIntHashTable *node_map,
                     BtorPtrHashTable *skolem_consts)
{
  int32_t i;
  char *symbol, *buf;
  size_t j, len;
  BtorNode *cur, *real_cur, *result, *quant, *param, *uf, **e;
  BtorNodePtrStack visit, quants, args, params;
  BtorMemMgr *mm;
  BtorIntHashTable *map;
  BtorHashTableData *d, *d_p;
  BtorSortIdStack sorts;
  BtorSortId tuple_s, fun_s;

  mm  = btor->mm;
  map = btor_hashint_map_new (mm);

  BTOR_INIT_STACK (mm, args);
  BTOR_INIT_STACK (mm, params);
  BTOR_INIT_STACK (mm, quants);
  BTOR_INIT_STACK (mm, sorts);
  BTOR_INIT_STACK (mm, visit);
  BTOR_PUSH_STACK (visit, root);

  while (!BTOR_EMPTY_STACK (visit))
  {
    cur      = BTOR_POP_STACK (visit);
    real_cur = btor_node_real_addr (cur);
    //      assert (!btor_node_is_quantifier (real_cur) ||
    //      !btor_node_is_inverted (cur));

    d = btor_hashint_map_get (map, real_cur->id);

    if (!d)
    {
      btor_hashint_map_add (map, real_cur->id);

      if (btor_node_is_forall (real_cur)) BTOR_PUSH_STACK (quants, cur);

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
        if (btor_node_is_param (real_cur))
        {
          symbol = btor_node_get_symbol (btor, real_cur);
          buf    = 0;
          if (btor_node_param_is_exists_var (real_cur))
          {
            if (symbol)
            {
              len = strlen (symbol) + 5;
              buf = btor_mem_malloc (mm, len);
              sprintf (buf, "sk(%s)", symbol);
            }

            /* substitute param with skolem function */
            if (BTOR_COUNT_STACK (quants) > 0)
            {
              for (j = 0; j < BTOR_COUNT_STACK (quants); j++)
              {
                quant = BTOR_PEEK_STACK (quants, j);
                d_p   = btor_hashint_map_get (map, quant->e[0]->id);
                assert (d_p);
                assert (d_p->as_ptr);
                param = d_p->as_ptr;
                BTOR_PUSH_STACK (params, param);
                BTOR_PUSH_STACK (sorts, param->sort_id);
              }

              tuple_s =
                  btor_sort_tuple (btor, sorts.start, BTOR_COUNT_STACK (sorts));
              fun_s = btor_sort_fun (btor, tuple_s, real_cur->sort_id);
              btor_sort_release (btor, tuple_s);

              uf = btor_exp_uf (btor, fun_s, buf);
              btor_sort_release (btor, fun_s);

              result = btor_exp_apply_n (
                  btor, uf, params.start, BTOR_COUNT_STACK (params));

              if (skolem_consts)
                btor_hashptr_table_add (skolem_consts,
                                        btor_node_copy (btor, uf));

              btor_node_release (btor, uf);
              BTOR_RESET_STACK (sorts);
              BTOR_RESET_STACK (params);
            }
            /* substitute param with variable in outermost scope */
            else
            {
              result = btor_exp_var (btor, real_cur->sort_id, buf);
              if (skolem_consts)
                btor_hashptr_table_add (skolem_consts,
                                        btor_node_copy (btor, result));
            }
          }
          else
          {
            if (symbol)
            {
              len = strlen (symbol) + 3;
              buf = btor_mem_malloc (mm, len);
              sprintf (buf, "%s!0", symbol);
            }
            result = btor_exp_param (btor, real_cur->sort_id, buf);
          }

          if (buf) btor_mem_freestr (mm, buf);
        }
        else
          result = btor_node_copy (btor, real_cur);
      }
      else if (btor_node_is_bv_slice (real_cur))
      {
        result = btor_exp_bv_slice (btor,
                                    e[0],
                                    btor_node_bv_slice_get_upper (real_cur),
                                    btor_node_bv_slice_get_lower (real_cur));
      }
      else if (btor_node_is_exists (real_cur))
      {
        assert (!btor_node_is_param (e[0]));
        result = btor_node_copy (btor, e[1]);
      }
      else
        result = btor_exp_create (btor, real_cur->kind, e, real_cur->arity);

      for (i = 0; i < real_cur->arity; i++) btor_node_release (btor, e[i]);

      d->as_ptr = btor_node_copy (btor, result);
      if (node_map)
      {
        assert (!btor_hashint_map_contains (node_map, real_cur->id));
        btor_hashint_map_add (node_map, real_cur->id)->as_int =
            btor_node_real_addr (result)->id;
      }
    PUSH_RESULT:

      if (btor_node_is_forall (real_cur))
      {
        quant = BTOR_POP_STACK (quants);
        assert (quant == cur);
      }

      result = btor_node_cond_invert (cur, result);
      assert (!btor_node_is_quantifier (result)
              || !btor_node_is_inverted (result));
      BTOR_PUSH_STACK (args, result);
    }
    else
    {
      assert (d->as_ptr);
      result = btor_node_copy (btor, d->as_ptr);
      goto PUSH_RESULT;
    }
  }
  assert (BTOR_COUNT_STACK (args) == 1);
  result = BTOR_POP_STACK (args);

  for (j = 0; j < map->size; j++)
  {
    if (!map->data[j].as_ptr) continue;
    btor_node_release (btor, map->data[j].as_ptr);
  }
  btor_hashint_map_delete (map);
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

  char *symbol, *buf;
  size_t i, len;
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
  cache = btor_hashint_map_new (mm);
  map   = btor_nodemap_new (btor);

  BTOR_INIT_STACK (mm, visit);

  /* push roots */
  btor_iter_hashptr_init (&it, btor->unsynthesized_constraints);
  while (btor_iter_hashptr_has_next (&it))
  {
    cur = btor_iter_hashptr_next (&it);
    BTOR_PUSH_STACK (visit, cur);
  }

  btor_init_substitutions (btor);
  BTOR_INIT_STACK (mm, quants);
  BTOR_INIT_STACK (mm, args);
  BTOR_INIT_STACK (mm, sorts);
  while (!BTOR_EMPTY_STACK (visit))
  {
    cur = btor_node_real_addr (BTOR_POP_STACK (visit));
    d   = btor_hashint_map_get (cache, cur->id);

    if (!d)
    {
      (void) btor_hashint_map_add (cache, cur->id);

      if (btor_node_is_forall (cur)) BTOR_PUSH_STACK (quants, cur);

      BTOR_PUSH_STACK (visit, cur);
      for (i = 0; i < cur->arity; i++) BTOR_PUSH_STACK (visit, cur->e[i]);
    }
    else if (d->as_int == 0)
    {
      d->as_int = 1;

      if (btor_node_is_forall (cur))
      {
        quant = BTOR_POP_STACK (quants);
        assert (quant == cur);
      }
      else if (btor_node_is_exists (cur) && BTOR_COUNT_STACK (quants) > 0)
      {
        param = cur->e[0];
        for (i = 0; i < BTOR_COUNT_STACK (quants); i++)
        {
          quant = BTOR_PEEK_STACK (quants, i);
          BTOR_PUSH_STACK (args, quant->e[0]);
          BTOR_PUSH_STACK (sorts, quant->e[0]->sort_id);
        }

        tuple_s = btor_sort_tuple (btor, sorts.start, BTOR_COUNT_STACK (sorts));
        fun_s   = btor_sort_fun (btor, tuple_s, param->sort_id);

        symbol = btor_node_get_symbol (btor, param);
        //	      printf ("%s\n", symbol);
        if (symbol)
        {
          len = strlen (symbol) + 5;
          buf = btor_mem_malloc (mm, len);
          sprintf (buf, "sk(%s)", symbol);
        }
        else
          buf = 0;
        uf  = btor_exp_uf (btor, fun_s, buf);
        app = btor_exp_apply_n (btor, uf, args.start, BTOR_COUNT_STACK (args));
        //	      printf ("%s -> %s\n", node2string (param), node2string
        //(uf));

        btor_nodemap_map (map, param, app);
        btor_mem_freestr (mm, buf);
        btor_sort_release (btor, tuple_s);
        btor_sort_release (btor, fun_s);
        btor_node_release (btor, uf);
        BTOR_RESET_STACK (sorts);
        BTOR_RESET_STACK (args);
      }
    }
  }

  btor_iter_hashptr_init (&it, btor->quantifiers);
  while (btor_iter_hashptr_has_next (&it))
  {
    cur = btor_iter_hashptr_next (&it);

    if (btor_node_is_forall (cur)) continue;

    /* exists quantifier in most outer scope */
    if (!btor_nodemap_mapped (map, cur->e[0])) continue;

    subst = btor_substitute_nodes (btor, btor_node_binder_get_body (cur), map);
    btor_nodemap_map (map, cur, subst);
    assert (!btor_hashptr_table_get (btor->substitutions, cur));
    btor_insert_substitution (btor, cur, subst, 0);
  }

  btor_substitute_and_rebuild (btor, btor->substitutions);
  btor_delete_substitutions (btor);

  btor_iter_nodemap_init (&nit, map);
  while (btor_iter_nodemap_has_next (&nit))
  {
    cur = btor_iter_nodemap_next_data (&nit)->as_ptr;
    btor_node_release (btor, cur);
  }

  btor_nodemap_delete (map);
  btor_hashint_map_delete (cache);
  BTOR_RELEASE_STACK (visit);
  BTOR_RELEASE_STACK (quants);
  BTOR_RELEASE_STACK (args);
  BTOR_RELEASE_STACK (sorts);
}
