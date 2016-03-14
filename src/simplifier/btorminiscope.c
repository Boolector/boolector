/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2016 Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "simplifier/btorminiscope.h"
#include "utils/btorhashint.h"
#include "utils/btoriter.h"
#include "utils/btorstack.h"

#define INV_KIND(k) \
  (k == BTOR_FORALL_NODE ? BTOR_EXISTS_NODE : BTOR_FORALL_NODE)

static BtorNode *
push_down_quantifier (Btor *btor, BtorNode *quantifier)
{
  assert (BTOR_IS_REGULAR_NODE (quantifier));
  assert (BTOR_IS_QUANTIFIER_NODE (quantifier));

  int i;
  BtorNode *param, *body, *real_body, *cur, *real_cur, *and, *e[2], *t;
  BtorNode *result, *p, *tmp;
  BtorNodeMap *subst_map;
  BtorNodePtrStack visit, args;
  BtorIntStack kind, args_kind;
  BtorMemMgr *mm;
  BtorIntHashTable *map, *cache;
  BtorNodeKind cur_kind, t_kind;

  mm        = btor->mm;
  param     = quantifier->e[0];
  body      = btor_binder_get_body (quantifier);
  real_body = BTOR_REAL_ADDR_NODE (body);
  /* cannot push down quantifier */
  if (!body || !BTOR_IS_AND_NODE (real_body)) return 0;

  cache = btor_new_int_hash_table (mm);
  map   = btor_new_int_hash_map (mm);
  //  printf ("quant: %s\n", node2string (quantifier));
  //  printf ("  body: %s\n", node2string (body));

  BTOR_INIT_STACK (visit);
  BTOR_INIT_STACK (args);
  BTOR_INIT_STACK (kind);
  BTOR_INIT_STACK (args_kind);
  BTOR_PUSH_STACK (mm, kind, quantifier->kind);
  BTOR_PUSH_STACK (mm, visit, body);
  /* push down quantifier */
  while (!BTOR_EMPTY_STACK (visit))
  {
    cur      = BTOR_POP_STACK (visit);
    real_cur = BTOR_REAL_ADDR_NODE (cur);
    cur_kind = BTOR_POP_STACK (kind);
    //      printf ("visit: %s (%s)\n", node2string (cur), cur_kind ==
    //      BTOR_FORALL_NODE ? "forall" : "exists");
    assert (real_cur->parameterized);

    // TODO (ma): push over quantifiers of same kind?
    if (!BTOR_IS_AND_NODE (real_cur))
    {
      //	  printf ("  no and\n");
      BTOR_PUSH_STACK (mm, args, btor_copy_exp (btor, cur));
      BTOR_PUSH_STACK (mm, args_kind, cur_kind);
      continue;
    }
    assert (cur_kind == BTOR_FORALL_NODE || cur_kind == BTOR_EXISTS_NODE);

    if (!btor_contains_int_hash_table (cache, real_cur->id))
    {
      btor_add_int_hash_table (cache, real_cur->id);
      BTOR_PUSH_STACK (mm, visit, cur);
      BTOR_PUSH_STACK (mm, kind, cur_kind);

      if (btor_param_is_free (btor, param, real_cur->e[0]))
      {
        //	      printf ("  free: %s\n", node2string (real_cur->e[0]));
        assert (!btor_param_is_free (btor, param, real_cur->e[1]));
        BTOR_PUSH_STACK (mm, args, btor_copy_exp (btor, real_cur->e[0]));
        BTOR_PUSH_STACK (mm, args_kind, 0);
        BTOR_PUSH_STACK (mm, visit, real_cur->e[1]);
        if (BTOR_IS_INVERTED_NODE (cur)) cur_kind = INV_KIND (cur_kind);
        BTOR_PUSH_STACK (mm, kind, cur_kind);
      }
      else if (btor_param_is_free (btor, param, real_cur->e[1]))
      {
        //	      printf ("  free: %s\n", node2string (real_cur->e[1]));
        assert (!btor_param_is_free (btor, param, real_cur->e[0]));
        BTOR_PUSH_STACK (mm, args, btor_copy_exp (btor, real_cur->e[1]));
        BTOR_PUSH_STACK (mm, args_kind, 0);
        BTOR_PUSH_STACK (mm, visit, real_cur->e[0]);
        if (BTOR_IS_INVERTED_NODE (cur)) cur_kind = INV_KIND (cur_kind);
        BTOR_PUSH_STACK (mm, kind, cur_kind);
      }
      /* match: \forall x . (e0[x] /\ e1[x])
       * result: (\forall x' . e0[x']) /\ (\forall x'' . e1[x''])
       */
      else if (BTOR_IS_FORALL_NODE_KIND (cur_kind)
               && !BTOR_IS_INVERTED_NODE (cur))
      {
        //	      printf ("  push forall\n");
        BTOR_PUSH_STACK (mm, visit, real_cur->e[0]);
        BTOR_PUSH_STACK (mm, kind, cur_kind);
        BTOR_PUSH_STACK (mm, visit, real_cur->e[1]);
        BTOR_PUSH_STACK (mm, kind, cur_kind);
      }
      else if (BTOR_IS_EXISTS_NODE_KIND (cur_kind)
               && BTOR_IS_INVERTED_NODE (cur))
      {
        //	      printf ("  push exists\n");
        //	      cur_kind = INV_KIND (cur_kind);
        BTOR_PUSH_STACK (mm, visit, real_cur->e[0]);
        BTOR_PUSH_STACK (mm, kind, cur_kind);
        BTOR_PUSH_STACK (mm, visit, real_cur->e[1]);
        BTOR_PUSH_STACK (mm, kind, cur_kind);
      }
      else
      {
        //	      printf ("  no push\n");
        BTOR_PUSH_STACK (mm, args, btor_copy_exp (btor, cur));
        BTOR_PUSH_STACK (mm, args_kind, cur_kind);
      }
    }
    else
    {
      assert (BTOR_COUNT_STACK (args) >= 2);
      for (i = 0; i < 2; i++)
      {
        t      = BTOR_POP_STACK (args);
        t_kind = BTOR_POP_STACK (args_kind);

        if (t_kind == 0)
          e[i] = btor_copy_exp (btor, t);
        else
        {
          assert (t_kind == BTOR_FORALL_NODE || t_kind == BTOR_EXISTS_NODE);
          p = btor_param_exp (btor, btor_get_exp_width (btor, param), 0);
          subst_map = btor_new_node_map (btor);
          btor_map_node (subst_map, param, p);
          tmp = btor_substitute_terms (btor, t, subst_map);
          btor_delete_node_map (subst_map);
          if (t_kind == BTOR_FORALL_NODE)
            e[i] = btor_forall_exp (btor, p, tmp);
          else
            e[i] = btor_exists_exp (btor, p, tmp);
          btor_release_exp (btor, p);
          btor_release_exp (btor, tmp);

          // TODO (ma):
          //    1) create new param p
          //    2) substitute 'param' with p in t1 and obtain t1'
          //    3) create new quantifier with p and t1'
        }
        //	      printf ("  %d: %s (%s)\n", i, node2string (e[i]),
        // node2string (t));
        btor_release_exp (btor, t);
      }

      and = btor_and_exp (btor, e[0], e[1]);
      btor_release_exp (btor, e[0]);
      btor_release_exp (btor, e[1]);

      //	  printf ("  result: %s\n", node2string (BTOR_COND_INVERT_NODE
      //(cur, and)));
      BTOR_PUSH_STACK (mm, args, BTOR_COND_INVERT_NODE (cur, and));
      BTOR_PUSH_STACK (mm, args_kind, 0);
    }
  }
  assert (BTOR_COUNT_STACK (args) == 1);
  result = BTOR_POP_STACK (args);

  btor_delete_int_hash_map (map);
  btor_delete_int_hash_table (cache);
  BTOR_RELEASE_STACK (mm, visit);
  BTOR_RELEASE_STACK (mm, args);
  BTOR_RELEASE_STACK (mm, args_kind);
  BTOR_RELEASE_STACK (mm, kind);
  return result;
}

void
btor_miniscope (Btor *btor)
{
  uint32_t i;
  BtorHashTableIterator it;
  BtorNode *cur, *subst;
  BtorNodePtrStack quants;
  BtorMemMgr *mm;

  if (btor->quantifiers->count == 0) return;

  mm = btor->mm;
  BTOR_INIT_STACK (quants);
  btor_init_node_hash_table_iterator (&it, btor->quantifiers);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    cur = btor_next_node_hash_table_iterator (&it);
    BTOR_PUSH_STACK (mm, quants, cur);
  }

  btor_init_substitutions (btor);
  for (i = 0; i < BTOR_COUNT_STACK (quants); i++)
  {
    cur   = BTOR_PEEK_STACK (quants, i);
    subst = push_down_quantifier (btor, cur);
    if (!subst) continue;
    btor_insert_substitution (btor, cur, subst, 0);
    btor_release_exp (btor, subst);
  }
  btor_substitute_and_rebuild (btor, btor->substitutions);
  btor_delete_substitutions (btor);
  BTOR_RELEASE_STACK (mm, quants);
}
