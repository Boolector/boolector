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
#include "utils/btoriter.h"
#include "utils/btorstack.h"

static bool
check_subst_cond (Btor *btor, BtorNode *param, BtorNode *subst)
{
  assert (btor);
  assert (param);
  assert (subst);
  return !BTOR_IS_INVERTED_NODE (param) && BTOR_IS_PARAM_NODE (param)
         && btor_param_is_forall_var (param)
         && btor_param_is_free (btor, param, subst);
}

static void
map_substitute_node (BtorNodeMap *map, BtorNode *left, BtorNode *right)
{
  bool inv = false;
  BtorNode *mapped;

  if (BTOR_IS_INVERTED_NODE (left))
  {
    inv  = true;
    left = BTOR_REAL_ADDR_NODE (left);
  }

  assert (BTOR_IS_REGULAR_NODE (left));
  while ((mapped = btor_mapped_node (map, left)))
  {
    left = mapped;
    if (BTOR_IS_INVERTED_NODE (left))
    {
      inv  = !inv;
      left = BTOR_REAL_ADDR_NODE (left);
    }
  }

  if ((mapped = btor_mapped_node (map, right))) right = mapped;

  if (inv) right = BTOR_INVERT_NODE (right);

  btor_map_node (map, left, right);
}

void
btor_der (Btor *btor)
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
        if (!BTOR_IS_INVERTED_NODE (cur) && BTOR_IS_BV_EQ_NODE (cur)
            && (check_subst_cond (btor, cur->e[0], cur->e[1])
                || check_subst_cond (btor, cur->e[1], cur->e[0])))
        {
          if (check_subst_cond (btor, cur->e[0], cur->e[1]))
          {
            map_substitute_node (map, cur->e[0], cur->e[1]);
            //		      printf ("subst %s -> %s\n", node2string
            //(cur->e[0]), node2string (cur->e[1]));
            continue;
          }
          else if (check_subst_cond (btor, cur->e[1], cur->e[0]))
          {
            map_substitute_node (map, cur->e[1], cur->e[0]);
            //		      printf ("subst %s -> %s\n", node2string
            //(cur->e[1]), node2string (cur->e[0]));
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
