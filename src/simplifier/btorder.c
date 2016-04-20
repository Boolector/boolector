/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2016 Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "simplifier/btorder.h"
#include "btorcore.h"
#include "utils/btorhashint.h"
#include "utils/btoriter.h"
#include "utils/btorstack.h"

static bool
occurs (Btor *btor, BtorNode *param, BtorNode *term)
{
  assert (BTOR_IS_REGULAR_NODE (param));
  assert (BTOR_IS_PARAM_NODE (param));

  bool res = false;
  uint32_t i;
  BtorNodePtrStack visit;
  BtorIntHashTable *mark;
  BtorNode *cur;
  BtorMemMgr *mm;

  mm   = btor->mm;
  mark = btor_new_int_hash_table (mm);
  BTOR_INIT_STACK (visit);
  BTOR_PUSH_STACK (mm, visit, term);
  while (!BTOR_EMPTY_STACK (visit))
  {
    cur = BTOR_REAL_ADDR_NODE (BTOR_POP_STACK (visit));

    if (!cur->parameterized || btor_contains_int_hash_table (mark, cur->id))
      continue;

    if (cur == param)
    {
      res = true;
      break;
    }

    btor_add_int_hash_table (mark, cur->id);
    for (i = 0; i < cur->arity; i++) BTOR_PUSH_STACK (mm, visit, cur->e[i]);
  }
  btor_delete_int_hash_table (mark);
  BTOR_RELEASE_STACK (mm, visit);
  return res;
}

static bool
check_subst_cond (Btor *btor, BtorNode *param, BtorNode *subst, bool is_cer)
{
  assert (btor);
  assert (param);
  assert (subst);
  // TODO: inverted check not needed here -x = y == x = -y
  return !BTOR_IS_INVERTED_NODE (param) && BTOR_IS_PARAM_NODE (param)
         && ((is_cer && btor_param_is_exists_var (param))
             || (!is_cer && btor_param_is_forall_var (param)))
         && !occurs (btor, param, subst);
}

#if 0
static void
map_substitute_node (BtorNodeMap * map, BtorNode * left, BtorNode * right)
{
  bool inv = false;
  BtorNode *mapped;

  if (BTOR_IS_INVERTED_NODE (left))
    {
      inv = true;
      left = BTOR_REAL_ADDR_NODE (left);
    }

  assert (BTOR_IS_REGULAR_NODE (left));
  while ((mapped = btor_mapped_node (map, left)))
    {
      left = mapped;
      if (BTOR_IS_INVERTED_NODE (left))
	{
	  inv = !inv;
	  left = BTOR_REAL_ADDR_NODE (left);
	}
    }

  if ((mapped = btor_mapped_node (map, right)))
    right = mapped;

  if (inv)
    right = BTOR_INVERT_NODE (right);

  btor_map_node (map, left, right);
}
#endif

static BtorNode *
find_subst (BtorIntHashTable *map, BtorNode *node)
{
  bool inv = false;
  BtorIntHashTableData *d;

  goto FIND_SUBST;

  while ((d = btor_get_int_hash_map (map, node->id)))
  {
    node = d->as_ptr;
  FIND_SUBST:
    if (BTOR_IS_INVERTED_NODE (node))
    {
      inv  = !inv;
      node = BTOR_INVERT_NODE (node);
    }
  }
  return BTOR_COND_INVERT_NODE (inv, node);
}

static void
map_subst_node (BtorIntHashTable *map,
                BtorIntHashTable *subst_scope,
                BtorNode *scope,
                BtorNode *left,
                BtorNode *right)
{
  BtorNodePtrStack *substs;
  BtorIntHashTableData *d;

  right = find_subst (map, right);
  if (BTOR_IS_INVERTED_NODE (left))
  {
    left  = BTOR_INVERT_NODE (left);
    right = BTOR_INVERT_NODE (right);
  }

  assert (BTOR_IS_REGULAR_NODE (left));

  // TODO (ma): overwrite subst if substitution is "better"?
  if (btor_contains_int_hash_map (map, left->id)) return;

  // printf ("subst: (%s) %s -> %s\n", node2string (scope), node2string (left),
  // node2string (right));

  //  assert (!btor_contains_int_hash_map (map, left->id));
  btor_add_int_hash_map (map, left->id)->as_ptr = right;

#if 0
  d = btor_get_int_hash_map (subst_scope, scope->id);

  if (!d)
    {
      BTOR_CNEW (subst_scope->mm, substs);
      BTOR_INIT_STACK (*substs);
      d = btor_add_int_hash_map (subst_scope, scope->id);
      d->as_ptr = substs;
    }
  else
    substs = d->as_ptr;

  BTOR_PUSH_STACK (subst_scope->mm, *substs, left);
#endif
}

static void
find_substitutions (Btor *btor,
                    BtorNode *root,
                    BtorIntHashTable *subst_map,
                    BtorIntHashTable *subst_scope,
                    bool is_cer)
{
  assert (btor);
  assert (root);
  assert (!BTOR_IS_QUANTIFIER_NODE (BTOR_REAL_ADDR_NODE (root)));
  assert (subst_map);

  BtorNode *cur, *real_cur, *top_and = 0;
  BtorNodePtrStack visit;
  BtorIntHashTable *cache;
  BtorMemMgr *mm;

  if (!BTOR_IS_AND_NODE (BTOR_REAL_ADDR_NODE (root)))
  {
    //    printf ("skip %s\n", node2string (root));
    return;
  }

  //  if (is_cer && BTOR_IS_INVERTED_NODE (root))
  //    return;
  //  else if (!is_cer && !BTOR_IS_INVERTED_NODE (root))
  //    return;
  if (is_cer)  // && !BTOR_IS_INVERTED_NODE (cur))
    top_and = BTOR_REAL_ADDR_NODE (root);
  else if (!is_cer && BTOR_IS_INVERTED_NODE (root))
    top_and = BTOR_REAL_ADDR_NODE (root);

  if (!top_and) return;

  mm    = btor->mm;
  cache = btor_new_int_hash_table (mm);
  BTOR_INIT_STACK (visit);
  BTOR_PUSH_STACK (mm, visit, top_and);
  while (!BTOR_EMPTY_STACK (visit))
  {
    cur      = BTOR_POP_STACK (visit);
    real_cur = BTOR_REAL_ADDR_NODE (cur);

    if (btor_contains_int_hash_table (cache, real_cur->id)) continue;

    //      printf ("visit: %s\n", node2string (cur));
    btor_add_int_hash_table (cache, real_cur->id);

    if (!BTOR_IS_INVERTED_NODE (cur) && BTOR_IS_AND_NODE (cur))
    {
      BTOR_PUSH_STACK (mm, visit, cur->e[0]);
      BTOR_PUSH_STACK (mm, visit, cur->e[1]);
    }
    else if (!BTOR_IS_INVERTED_NODE (cur) && BTOR_IS_BV_EQ_NODE (cur))
    {
      if (check_subst_cond (btor, cur->e[0], cur->e[1], is_cer))
        map_subst_node (subst_map, subst_scope, top_and, cur->e[0], cur->e[1]);
      else if (check_subst_cond (btor, cur->e[1], cur->e[0], is_cer))
        map_subst_node (subst_map, subst_scope, top_and, cur->e[1], cur->e[0]);
    }
  }
  BTOR_RELEASE_STACK (mm, visit);
  btor_delete_int_hash_table (cache);
}

// TODO: reset cached nodes after closing subst scope
static BtorNode *
der_cer_node (Btor *btor, BtorNode *root, bool is_cer)
{
  uint32_t i, num_quant_vars = 0, num_occ = 0;
  BtorNode *cur, *real_cur, *e[3], *result, *n;
  BtorNodePtrStack visit, reset, *substs;
  BtorMemMgr *mm;
  BtorIntHashTable *map, *subst_map, *subst_scope, *cache;
  BtorIntHashTableData *cur_d, *d, d_s;

  mm          = btor->mm;
  map         = btor_new_int_hash_map (mm);
  subst_map   = btor_new_int_hash_map (mm);
  subst_scope = btor_new_int_hash_map (mm);
  cache       = btor_new_int_hash_table (mm);

  BTOR_INIT_STACK (reset);
  BTOR_INIT_STACK (visit);
  BTOR_PUSH_STACK (mm, visit, root);
  while (!BTOR_EMPTY_STACK (visit))
  {
    cur      = BTOR_POP_STACK (visit);
    real_cur = BTOR_REAL_ADDR_NODE (cur);
    cur_d    = btor_get_int_hash_map (map, real_cur->id);

    if (!cur_d)
    {
      //	  printf ("_visit1: %s\n", node2string (cur));
      btor_add_int_hash_map (map, real_cur->id);

      if (real_cur->arity > 0) BTOR_PUSH_STACK (mm, reset, real_cur);
      //	  if (BTOR_IS_AND_NODE (real_cur))
      if (BTOR_IS_QUANTIFIER_NODE (real_cur)
          && !BTOR_IS_QUANTIFIER_NODE (BTOR_REAL_ADDR_NODE (real_cur->e[1])))
      {
        //	    printf ("find substs: %s\n", node2string (cur));
        find_substitutions (
            btor, real_cur->e[1], subst_map, subst_scope, is_cer);
      }

#if 0
	  if (BTOR_IS_QUANTIFIER_NODE (real_cur)
	      && !BTOR_IS_QUANTIFIER_NODE (
		    BTOR_REAL_ADDR_NODE (real_cur->e[1])))
	    {
	    printf ("QUANT: %s\n", node2string (real_cur));
	    find_substitutions (btor, real_cur->e[1], subst_map, subst_scope, is_cer);
	    }
#endif

      if ((is_cer && BTOR_IS_EXISTS_NODE (real_cur))
          || (!is_cer && BTOR_IS_FORALL_NODE (real_cur)))
        num_quant_vars++;

#if 0
	  if (!BTOR_IS_INVERTED_NODE (cur)
	      && BTOR_IS_BV_EQ_NODE (real_cur)
	      && (BTOR_IS_PARAM_NODE (BTOR_REAL_ADDR_NODE (real_cur->e[0]))
		  || BTOR_IS_PARAM_NODE (BTOR_REAL_ADDR_NODE (real_cur->e[1]))))
	    {
	      if (BTOR_IS_PARAM_NODE (BTOR_REAL_ADDR_NODE (real_cur->e[0])))
		printf ("%s (0: %d, %d)\n", node2string (cur),
			btor_param_is_forall_var (real_cur->e[0]),
			btor_param_is_exists_var (real_cur->e[0]));
	      else if (BTOR_IS_PARAM_NODE (BTOR_REAL_ADDR_NODE (real_cur->e[1])))
		printf ("%s (1: %d, %d)\n", node2string (cur),
			btor_param_is_forall_var (real_cur->e[1]),
			btor_param_is_exists_var (real_cur->e[1]));
	    }
#endif

      BTOR_PUSH_STACK (mm, visit, real_cur);
      for (i = 0; i < real_cur->arity; i++)
        BTOR_PUSH_STACK (mm, visit, real_cur->e[i]);

      /* we need to rebuild the substitution first */
      if ((d = btor_get_int_hash_map (subst_map, real_cur->id)))
        BTOR_PUSH_STACK (mm, visit, d->as_ptr);
    }
    else if (!cur_d->as_ptr)
    {
      //	  printf ("_visit2: %s\n", node2string (cur));
      for (i = 0; i < real_cur->arity; i++)
      {
        e[i] = find_subst (subst_map, real_cur->e[i]);
        //	      if (btor_contains_int_hash_map (subst_map,
        // BTOR_REAL_ADDR_NODE (real_cur->e[i])->id))
        //		printf ("----> subst: %s -> %s\n", node2string
        //(real_cur->e[i]), node2string (e[i]));
        d = btor_get_int_hash_map (map, BTOR_REAL_ADDR_NODE (e[i])->id);
        assert (d);
        e[i] = BTOR_COND_INVERT_NODE (e[i], d->as_ptr);
      }
      if (real_cur->arity == 0)
      {
        /* 'real_cur' get substituted anyway, so we don't need to create
         * a new parameter */
        if (0 && btor_contains_int_hash_map (subst_map, real_cur->id))
        {
          assert (BTOR_IS_PARAM_NODE (real_cur));
          continue;
        }

        if (BTOR_IS_PARAM_NODE (real_cur))
          result =
              btor_param_exp (btor, btor_get_exp_width (btor, real_cur), 0);
        else
          result = btor_copy_exp (btor, real_cur);
      }
      else if (BTOR_IS_SLICE_NODE (real_cur))
        result = btor_slice_exp (btor,
                                 e[0],
                                 btor_slice_get_upper (real_cur),
                                 btor_slice_get_lower (real_cur));
      /* param of quantifier got substituted */
      else if (0 && BTOR_IS_QUANTIFIER_NODE (real_cur)
               && btor_contains_int_hash_map (subst_map, real_cur->e[0]->id))
        result = btor_copy_exp (btor, e[1]);
      else
      {
        result = btor_create_exp (btor, real_cur->kind, e, real_cur->arity);
        //	    if (BTOR_IS_QUANTIFIER_NODE (real_cur)
        //		&& !BTOR_IS_QUANTIFIER_NODE (BTOR_REAL_ADDR_NODE
        //(result))) 	      printf ("%s ::: %s\n", node2string (real_cur),
        // node2string (result));
      }
      //	  printf ("  result: %s\n", node2string (result));
      cur_d->as_ptr = result;

#if 0
	  d = btor_get_int_hash_map (subst_scope, real_cur->id);
	  if (d)
	    {
//	      printf ("close scope: %s\n", node2string (real_cur));
	      assert (BTOR_IS_AND_NODE (real_cur));
	      substs = d->as_ptr;
	      assert (substs);
	      btor_remove_int_hash_map (subst_scope, real_cur->id, 0);

	      while (!BTOR_EMPTY_STACK (*substs))
		{
		  n = BTOR_POP_STACK (*substs);
//		  printf ("  remove: %s\n", node2string (n));
		  assert (btor_contains_int_hash_map (subst_map, n->id));
		  btor_remove_int_hash_map (subst_map, n->id, 0);
		  num_occ++;
		}
	      BTOR_RELEASE_STACK (mm, *substs);
	      BTOR_DELETE (mm, substs);

	      /* reset cache for this substitution scope */
	      n = BTOR_POP_STACK (reset);
	      printf ("reset: %s\n", node2string (n));
	      while (n != real_cur)
		{
		  printf ("reset: %s\n", node2string (n));
		  btor_remove_int_hash_map (map, n->id, &d_s);
		  assert (d_s.as_ptr);
		  btor_release_exp (btor, d_s.as_ptr);
		  assert (!BTOR_EMPTY_STACK (reset));
		  n = BTOR_POP_STACK (reset);
		}
	    }
#endif
    }
  }
  assert (subst_scope->count == 0);
  assert (subst_map->count == 0);
  d = btor_get_int_hash_map (map, BTOR_REAL_ADDR_NODE (root)->id);
  assert (d);
  assert (d->as_ptr);
  result = btor_copy_exp (btor, BTOR_COND_INVERT_NODE (root, d->as_ptr));
  assert (BTOR_REAL_ADDR_NODE (result)->parameterized
          == BTOR_REAL_ADDR_NODE (root)->parameterized);

  printf ("substituted %u out of %u %s variables\n",
          num_occ,  // subst_map->count,
          num_quant_vars,
          is_cer ? "existential" : "universal");

  for (i = 0; i < map->size; i++)
  {
    if (!map->data[i].as_ptr) continue;
    btor_release_exp (btor, map->data[i].as_ptr);
  }
  btor_delete_int_hash_map (map);
  btor_delete_int_hash_map (subst_map);
  btor_delete_int_hash_map (subst_scope);
  btor_delete_int_hash_table (cache);
  BTOR_RELEASE_STACK (mm, visit);
  BTOR_RELEASE_STACK (mm, reset);
  return result;
}

BtorNode *
btor_der_node (Btor *btor, BtorNode *root)
{
  return der_cer_node (btor, root, false);
}

BtorNode *
btor_cer_node (Btor *btor, BtorNode *root)
{
  return der_cer_node (btor, root, true);
}

#if 0
void
btor_der (Btor * btor)
{
  BtorHashTableIterator it;
  BtorNode *cur, *body, *subst, *tmp, *and;
  BtorNodePtrStack quantifiers, leafs, visit;
  BtorMemMgr *mm;
  BtorNodeMap *map;

  BTOR_INIT_STACK (quantifiers);
  mm = btor->mm;
  btor_init_node_hash_table_iterator (&it, btor->quantifiers);
  while (btor_has_next_hash_table_iterator (&it))
    {
      cur = btor_next_node_hash_table_iterator (&it);
      if (cur->parameterized) continue;
      BTOR_PUSH_STACK (mm, quantifiers, cur);
    }

  btor_init_substitutions (btor);
  while (!BTOR_EMPTY_STACK (quantifiers))
    {
      cur = BTOR_POP_STACK (quantifiers);
//      printf ("%s\n", node2string (cur));
      body = btor_binder_get_body (cur);

      if (!BTOR_IS_INVERTED_NODE (body)
	  || !BTOR_IS_AND_NODE (BTOR_REAL_ADDR_NODE (body)))
	continue;

      map = btor_new_node_map (btor);
      BTOR_INIT_STACK (leafs);
      BTOR_INIT_STACK (visit);
      BTOR_PUSH_STACK (mm, visit, BTOR_REAL_ADDR_NODE (body));
      while (!BTOR_EMPTY_STACK (visit))
	{
	  cur = BTOR_POP_STACK (visit);

	  if (!BTOR_IS_INVERTED_NODE (cur) && BTOR_IS_AND_NODE (cur))
	    {
	      BTOR_PUSH_STACK (mm, visit, cur->e[0]);
	      BTOR_PUSH_STACK (mm, visit, cur->e[1]);
	    }
	  else
	    {
	      if (!BTOR_IS_INVERTED_NODE (cur)
		  && BTOR_IS_BV_EQ_NODE (cur)
		  && (check_subst_cond (btor, cur->e[0], cur->e[1])
		      || check_subst_cond (btor, cur->e[1], cur->e[0])))
		{
		  if (check_subst_cond (btor, cur->e[0], cur->e[1])) 
		    {
		      map_substitute_node (map, cur->e[0], cur->e[1]);
//		      printf ("subst %s -> %s\n", node2string (cur->e[0]), node2string (cur->e[1]));
		      continue;
		    }
		  else if (check_subst_cond (btor, cur->e[1], cur->e[0]))
		    {
		      map_substitute_node (map, cur->e[1], cur->e[0]);
//		      printf ("subst %s -> %s\n", node2string (cur->e[1]), node2string (cur->e[0]));
		      continue;
		    }
		}
//	      printf ("push leaf: %s\n", node2string (cur));
	      BTOR_PUSH_STACK (mm, leafs, cur);
	    }
	}
      BTOR_RELEASE_STACK (mm, visit);

      if (map->table->count > 0)
	{
	  subst = 0;

//	  printf ("%d leafs\n", BTOR_COUNT_STACK (leafs));
	  while (!BTOR_EMPTY_STACK (leafs))
	    {
	      cur = BTOR_POP_STACK (leafs);
//	      printf ("############################\n");
	      tmp = btor_substitute_terms (btor, cur, map);

	      if (subst)
		{
		  and = btor_and_exp (btor, subst, tmp);
		  btor_release_exp (btor, subst);
		  btor_release_exp (btor, tmp);
		  subst = and;
		}
	      else
		subst = tmp;
	    }

	  assert (subst);
	  btor_insert_substitution (btor, body, subst, 0);
	  btor_release_exp (btor, subst);
	}
      btor_delete_node_map (map);
      BTOR_RELEASE_STACK (mm, leafs);
    }

  btor_substitute_and_rebuild (btor, btor->substitutions);
  btor_delete_substitutions (btor);
  BTOR_RELEASE_STACK (mm, quantifiers);
}
#endif
