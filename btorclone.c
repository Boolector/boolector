#include "btoraig.h"
#include "btoraigvec.h"
#include "btorexp.h"
#include "btorhash.h"
#include "btormap.h"
#include "btorstack.h"

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>

BTOR_DECLARE_STACK (NodePtrPtr, BtorNode **);
BTOR_DECLARE_STACK (AIGPtrPtr, BtorAIG **);

static BtorAIG *
clone_aig (Btor *btor,
           Btor *clone,
           BtorAIG *aig,
           BtorAIGPtrPtrStack *nexts,
           BtorAIGMap *aig_map)
{
  assert (aig);
  assert (aig_map);

  int i;
  BtorAIG *res, *tmp;
  BtorMemMgr *mm, *cmm;

  mm  = btor->mm;
  cmm = btor->mm;

  BTOR_NEWN (cmm, res, 1);
  memcpy (aig, res, sizeof *aig);

  for (i = 0; i < 2 && aig->children[i]; i++)
  {
    tmp = btor_mapped_aig (aig_map, aig->children[i]);
    assert (tmp);
    res->children[i] = tmp;
  }

  BTOR_PUSH_STACK (mm, *nexts, &aig->next);

  return res;
}

static BtorAIGVec *
clone_av (Btor *btor,
          Btor *clone,
          BtorAIGVec *av,
          BtorAIGPtrPtrStack *nexts,
          BtorAIGMap *aig_map)
{
  int i;
  BtorAIG *cur;
  BtorAIGVec *res;
  BtorAIGPtrStack stack, unmark_stack;
  BtorMemMgr *mm, *cmm;

  mm  = btor->mm;
  cmm = clone->mm;

  BTOR_INIT_STACK (stack);
  BTOR_INIT_STACK (unmark_stack);

  BTOR_NEWN (cmm, res, 1);
  memcpy (av, res, sizeof *av);

  for (i = 0; i < av->len; i++)
  {
    BTOR_PUSH_STACK (mm, stack, av->aigs[i]);
    while (!BTOR_EMPTY_STACK (stack))
    {
      cur = BTOR_POP_STACK (stack);

      if (cur->clone_mark >= 2 || btor_mapped_aig (aig_map, cur)) continue;

      if (cur->clone_mark == 0)
      {
        cur->clone_mark = 1;
        BTOR_PUSH_STACK (mm, stack, cur);
        BTOR_PUSH_STACK (mm, unmark_stack, cur);

        BTOR_PUSH_STACK (mm, stack, cur->children[0]);
        BTOR_PUSH_STACK (mm, stack, cur->children[1]);
      }
      else
      {
        assert (cur->clone_mark == 1);
        cur->clone_mark = 2;
        btor_map_aig (
            btor, aig_map, cur, clone_aig (btor, clone, cur, nexts, aig_map));
      }
    }
    res->aigs[i] = btor_mapped_aig (aig_map, res->aigs[i]);
    assert (res->aigs[i]);
  }

  /* reset mark flags */
  while (!BTOR_EMPTY_STACK (unmark_stack))
  {
    cur = BTOR_POP_STACK (unmark_stack);
    assert (cur->clone_mark == 2);
    cur->clone_mark = 0;
  }

  return res;
}

static BtorNode *
clone_exp (Btor *btor,
           Btor *clone,
           BtorNode *exp,
           BtorNodePtrPtrStack *parents,
           BtorAIGPtrPtrStack *nexts,
           BtorNodeMap *exp_map,
           BtorAIGMap *aig_map)
{
  assert (btor);
  assert (clone);
  assert (exp);
  assert (parents);
  assert (exp_map);
  assert (aig_map);

  int i, len;
  BtorNode *res, *real_exp, *exp1, *exp2;
  BtorMemMgr *mm, *cmm;

  mm  = btor->mm;
  cmm = clone->mm;

  real_exp = BTOR_REAL_ADDR_NODE (exp);
  assert (!BTOR_IS_PROXY_NODE (real_exp));

  res = btor_malloc (cmm, real_exp->bytes);
  memcpy (real_exp, res, sizeof *real_exp);

  if (real_exp->bits)
  {
    len = strlen (real_exp->bits);
    BTOR_NEWN (cmm, res->bits, len);
    for (i = 0; i < len; i++) res->bits[i] = real_exp->bits[i];
  }

  /* Note: no need to cache aig vectors here (exp->av is unique to exp). */
  if (!BTOR_IS_ARRAY_NODE (real_exp))
    res->av = clone_av (btor, clone, res->av, nexts, aig_map);

  exp1 = btor_mapped_node (exp_map, real_exp->next);
  assert (exp1);
  res->next = exp1;

  BTOR_PUSH_STACK (mm, *parents, &real_exp->parent);

  assert (!real_exp->simplified);

  res->btor = clone;

  BTOR_PUSH_STACK (mm, *parents, &real_exp->first_parent);
  BTOR_PUSH_STACK (mm, *parents, &real_exp->last_parent);

  if (!BTOR_IS_BV_CONST_NODE (real_exp) && !BTOR_IS_BV_VAR_NODE (real_exp)
      && !BTOR_IS_ARRAY_VAR_NODE (real_exp) && !BTOR_IS_PARAM_NODE (real_exp))
  {
    if (real_exp->arity)
    {
      for (i = 0; i < real_exp->arity; i++)
      {
        exp1 = btor_mapped_node (exp_map, BTOR_REAL_ADDR_NODE (real_exp->e[i]));
        assert (exp);
        res->e[i] = BTOR_IS_INVERTED_NODE (real_exp->e[i])
                        ? BTOR_INVERT_NODE (real_exp->e[i])
                        : exp;
      }
    }
    else
    {
      res->symbol = btor_strdup (cmm, real_exp->symbol);
      if (BTOR_IS_ARRAY_EQ_NODE (real_exp))
      {
        exp1 = btor_mapped_node (exp_map, real_exp->vreads->exp1);
        assert (exp1);
        exp2 = btor_mapped_node (exp_map, real_exp->vreads->exp2);
        assert (exp2);
        res->vreads = new_exp_pair (clone, exp1, exp2);
      }
    }

    for (i = 0; i < real_exp->arity; i++)
    {
      BTOR_PUSH_STACK (mm, *parents, &real_exp->prev_parent[i]);
      BTOR_PUSH_STACK (mm, *parents, &real_exp->next_parent[i]);
    }
  }

  if (BTOR_IS_ARRAY_NODE (real_exp))
  {
    BTOR_PUSH_STACK (mm, *parents, &real_exp->first_aeq_acond_parent);
    BTOR_PUSH_STACK (mm, *parents, &real_exp->last_aeq_acond_parent);

    if (!BTOR_IS_ARRAY_VAR_NODE (real_exp))
    {
      for (i = 0; i < real_exp->arity; i++)
      {
        BTOR_PUSH_STACK (mm, *parents, &real_exp->prev_aeq_acond_parent[i]);
        BTOR_PUSH_STACK (mm, *parents, &real_exp->next_aeq_acond_parent[i]);
      }
    }
  }

  return res;
}

static void
clone_constraints (Btor *btor,
                   Btor *clone,
                   BtorNodeMap *exp_map,
                   BtorAIGMap *aig_map)
{
  assert (btor);
  assert (clone);
  assert (exp_map);
  assert (aig_map);

  int i;
  BtorNode *cur, *real_cur, *cloned_exp, **parent;
  BtorNodePtrStack stack, unmark_stack;
  BtorNodePtrPtrStack parents;
  BtorAIG **next, *cloned_aig;
  BtorAIGPtrPtrStack nexts;
  BtorPtrHashBucket *b;
  BtorPtrHashTable **c, **r;
  BtorMemMgr *mm;

  BtorPtrHashTable *constraints[]     = {btor->unsynthesized_constraints,
                                     btor->synthesized_constraints,
                                     btor->embedded_constraints,
                                     NULL},
                   *res_constraints[] = {clone->unsynthesized_constraints,
                                         clone->synthesized_constraints,
                                         clone->embedded_constraints,
                                         NULL};

  BTOR_INIT_STACK (stack);
  BTOR_INIT_STACK (unmark_stack);
  BTOR_INIT_STACK (parents);
  BTOR_INIT_STACK (nexts);

  mm = btor->mm;

  for (c = constraints, r = res_constraints; *c; c++, r++)
  {
    for (b = (*c)->first; b; b = b->next)
    {
      cur = (BtorNode *) b->key;
      BTOR_PUSH_STACK (mm, stack, cur);
      while (!BTOR_EMPTY_STACK (stack))
      {
        cur      = BTOR_POP_STACK (stack);
        real_cur = BTOR_REAL_ADDR_NODE (cur);

        if (real_cur->clone_mark >= 2) continue;

        if (real_cur->clone_mark == 0)
        {
          real_cur->clone_mark = 1;
          BTOR_PUSH_STACK (mm, stack, cur);
          BTOR_PUSH_STACK (mm, unmark_stack, real_cur);

          if (BTOR_IS_ARRAY_EQ_NODE (real_cur))
          {
            BTOR_PUSH_STACK (mm, stack, real_cur->vreads->exp1);
            BTOR_PUSH_STACK (mm, stack, real_cur->vreads->exp2);
          }

          for (i = 0; i < real_cur->arity; i++)
            BTOR_PUSH_STACK (mm, stack, real_cur->e[i]);
        }
        else
        {
          assert (real_cur->clone_mark == 1);
          real_cur->clone_mark = 2;

          cloned_exp =
              clone_exp (btor, clone, cur, &parents, &nexts, exp_map, aig_map);
          btor_map_node (btor, exp_map, real_cur, cloned_exp);
        }
      }

      cloned_exp = btor_mapped_node (exp_map, b->key);
      assert (cloned_exp);
      btor_insert_in_ptr_hash_table (*r, cloned_exp);
    }
  }

  /* update parent pointers of expressions */
  while (!BTOR_EMPTY_STACK (parents))
  {
    parent     = BTOR_POP_STACK (parents);
    cloned_exp = btor_mapped_node (exp_map, *parent);
    assert (cloned_exp);
    *parent = cloned_exp;
  }

  /* update next pointers of aigs */
  while (!BTOR_EMPTY_STACK (nexts))
  {
    next       = BTOR_POP_STACK (nexts);
    cloned_aig = btor_mapped_aig (aig_map, *next);
    assert (cloned_aig);
    *next = cloned_aig;
  }

  /* reset mark flags */
  while (!BTOR_EMPTY_STACK (unmark_stack))
  {
    cur = BTOR_POP_STACK (unmark_stack);
    assert (cur->clone_mark == 2);
    cur->clone_mark = 0;
  }
}

//
//
// Btor *
// btor_clone_btor (Btor * btor)
//{
//  Btor *clone;
//  //BtorMemMgr *mm;
//  BtorNodeMap *exp_map, *aig_map, *av_map;
//
//  //mm = btor->mm;
//  exp_map = btor_new_node_map (btor);
//  aig_map = btor_new_node_map (btor);
//  av_map = btor_new_node_map (btor);
//
//  clone = btor_new_btor ();
//  memcpy (&clone->bv_lambda_id, &btor->bv_lambda_id,
//	  (char *) &btor->lod_cache - (char *) &btor->bv_lambda_id);
//  memcpy (&clone->stats, &btor->stats,
//	  btor + sizeof *btor -  (char *) &btor->stats);
//
//  // TODO clone top-level constraints
//
//
//
//
//
//}
