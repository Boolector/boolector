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
check_subst_cond (Btor *btor, BtorNode *param, BtorNode *subst)
{
  assert (btor);
  assert (param);
  assert (subst);
  // TODO: inverted check not needed here -x = y == x = -y
  return !BTOR_IS_INVERTED_NODE (param) && BTOR_IS_PARAM_NODE (param)
         && btor_param_is_forall_var (param)
         && btor_param_is_free (btor, param, subst);
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
map_subst_node (BtorIntHashTable *map, BtorNode *left, BtorNode *right)
{
  right = find_subst (map, right);
  if (BTOR_IS_INVERTED_NODE (left))
  {
    left  = BTOR_INVERT_NODE (left);
    right = BTOR_INVERT_NODE (right);
  }

  assert (BTOR_IS_REGULAR_NODE (left));
  btor_add_int_hash_map (map, left->id)->as_ptr = right;
}

static void
find_substitutions (Btor *btor, BtorNode *root, BtorIntHashTable *subst_map)
{
  assert (BTOR_IS_REGULAR_NODE (root));
  assert (BTOR_IS_QUANTIFIER_NODE (root));
  assert (subst_map);

  BtorNode *body, *cur, *real_cur, *e0, *e1;
  BtorNodePtrStack visit;
  BtorIntHashTable *cache;
  BtorMemMgr *mm;

  body = btor_binder_get_body (root);

  if (!BTOR_IS_INVERTED_NODE (body)
      || !BTOR_IS_AND_NODE (BTOR_REAL_ADDR_NODE (body)))
    return;

  mm    = btor->mm;
  cache = btor_new_int_hash_table (mm);

  BTOR_INIT_STACK (visit);
  BTOR_PUSH_STACK (mm, visit, BTOR_REAL_ADDR_NODE (body));
  while (!BTOR_EMPTY_STACK (visit))
  {
    cur      = BTOR_POP_STACK (visit);
    real_cur = BTOR_REAL_ADDR_NODE (cur);

    if (btor_contains_int_hash_table (cache, real_cur->id)) continue;

    btor_add_int_hash_table (cache, real_cur->id);

    if (!BTOR_IS_INVERTED_NODE (cur) && BTOR_IS_AND_NODE (cur))
    {
      BTOR_PUSH_STACK (mm, visit, cur->e[0]);
      BTOR_PUSH_STACK (mm, visit, cur->e[1]);
    }
    else if (!BTOR_IS_INVERTED_NODE (cur) && BTOR_IS_BV_EQ_NODE (cur))
    {
      e0 = cur->e[0];  // find_subst (map, cur->e[0]);
      e1 = cur->e[1];  // find_subst (map, cur->e[1]);
      if (check_subst_cond (btor, e0, e1))
      {
        map_subst_node (subst_map, e0, e1);
        //	      printf ("subst %s -> %s\n", node2string (cur->e[0]),
        // node2string (cur->e[1]));
        continue;
      }
      else if (check_subst_cond (btor, e1, e0))
      {
        map_subst_node (subst_map, e1, e0);
        //	      printf ("subst %s -> %s\n", node2string (cur->e[1]),
        // node2string (cur->e[0]));
        continue;
      }
    }
  }
  BTOR_RELEASE_STACK (mm, visit);
  btor_delete_int_hash_table (cache);
}

BtorNode *
btor_der_node (Btor *btor, BtorNode *root)
{
  uint32_t i, num_univeral_quants = 0;
  BtorNode *cur, *e[3], *result;
  BtorNodePtrStack visit;
  BtorMemMgr *mm;
  BtorIntHashTable *map, *subst_map;
  BtorIntHashTableData *cur_d, *d;

  mm        = btor->mm;
  map       = btor_new_int_hash_map (mm);
  subst_map = btor_new_int_hash_map (mm);

  BTOR_INIT_STACK (visit);
  BTOR_PUSH_STACK (mm, visit, root);
  while (!BTOR_EMPTY_STACK (visit))
  {
    cur   = BTOR_REAL_ADDR_NODE (BTOR_POP_STACK (visit));
    cur_d = btor_get_int_hash_map (map, cur->id);

    if (!cur_d)
    {
      btor_add_int_hash_map (map, cur->id);

      if (BTOR_IS_QUANTIFIER_NODE (cur)
          && !BTOR_IS_QUANTIFIER_NODE (BTOR_REAL_ADDR_NODE (cur->e[1])))
        find_substitutions (btor, cur, subst_map);

      if (BTOR_IS_FORALL_NODE (cur)) num_univeral_quants++;

      BTOR_PUSH_STACK (mm, visit, cur);
      for (i = 0; i < cur->arity; i++) BTOR_PUSH_STACK (mm, visit, cur->e[i]);

      /* we need to rebuild the substitution first */
      if ((d = btor_get_int_hash_map (subst_map, cur->id)))
        BTOR_PUSH_STACK (mm, visit, d->as_ptr);
    }
    else if (!cur_d->as_ptr)
    {
      for (i = 0; i < cur->arity; i++)
      {
        e[i] = find_subst (subst_map, cur->e[i]);
        d    = btor_get_int_hash_map (map, BTOR_REAL_ADDR_NODE (e[i])->id);
        assert (d);
        e[i] = BTOR_COND_INVERT_NODE (e[i], d->as_ptr);
      }
      if (cur->arity == 0)
      {
        /* 'cur' get substituted anyway, so we don't need to create a
         * new parameter */
        if (btor_contains_int_hash_map (subst_map, cur->id))
        {
          assert (BTOR_IS_PARAM_NODE (cur));
          continue;
        }

        if (BTOR_IS_PARAM_NODE (cur))
          result = btor_param_exp (btor, btor_get_exp_width (btor, cur), 0);
        else
          result = btor_copy_exp (btor, cur);
      }
      else if (BTOR_IS_SLICE_NODE (cur))
        result = btor_slice_exp (
            btor, e[0], btor_slice_get_upper (cur), btor_slice_get_lower (cur));
      /* param of quantifier got substituted */
      else if (BTOR_IS_QUANTIFIER_NODE (cur)
               && btor_contains_int_hash_map (subst_map, cur->e[0]->id))
        result = btor_copy_exp (btor, e[1]);
      else
        result = btor_create_exp (btor, cur->kind, cur->arity, e);
      cur_d->as_ptr = result;
    }
  }
  d = btor_get_int_hash_map (map, BTOR_REAL_ADDR_NODE (root)->id);
  assert (d);
  assert (d->as_ptr);
  result = btor_copy_exp (btor, BTOR_COND_INVERT_NODE (root, d->as_ptr));
  assert (BTOR_REAL_ADDR_NODE (result)->parameterized
          == BTOR_REAL_ADDR_NODE (root)->parameterized);

  printf ("substituted %u out of %u universal variables\n",
          subst_map->count,
          num_univeral_quants);

  for (i = 0; i < map->size; i++)
  {
    if (!map->data[i].as_ptr) continue;
    btor_release_exp (btor, map->data[i].as_ptr);
  }
  btor_delete_int_hash_map (map);
  btor_delete_int_hash_map (subst_map);
  BTOR_RELEASE_STACK (mm, visit);
  return result;
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
