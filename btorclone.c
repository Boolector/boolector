#include <btorexp.h>
#include <btormap.h>
#include <btorstack.h>

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>

BTOR_DECLARE_STACK (NodePtrPtr, BtorNode **);

// TODO
static BtorAIGVec *
clone_av ()
{
  return 0;
}

static BtorNode *
clone_exp (Btor *btor,
           Btor *clone,
           BtorNode *exp,
           BtorNodePtrPtrStack *parents,
           BtorNodeMap *exp_map,
           BtorNodeMap *aigmap,
           BtorNodeMap *avmap)
{
  assert (clone);
  assert (exp);

  int i, len;
  BtorNode *res, *real_exp, *exp, *exp2;
  BtorMemMgr *mm, *cmm;

  mm  = btor->mm;
  cmm = clone->m;

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

  if (!BTOR_IS_ARRAY_NODE (real_exp))
    // TODO clone av

    exp = btor_mapped_node (exp_map, real_exp->next);
  assert (exp);
  res->next = exp;

  BTOR_PUSH_STACK (mm, *parents, &real_exp->parent);

  assert (!real_exp->simplified);

  res->btor = clone;

  BTOR_PUSH_STACK (mm, *parents, real_exp->first_parent);
  BTOR_PUSH_STACK (mm, *parents, real_exp->last_parent);

  if (!BTOR_IS_BV_CONST_NODE (real_exp) && !BTOR_IS_BV_VAR_NODE (real_exp)
      && !BTOR_IS_ARRAY_VAR_NODE (real_exp) && !BTOR_IS_PARAM_NODE (real_exp))
  {
    if (real_exp->arity)
    {
      for (i = 0; i < real_exp->arity; i++)
      {
        exp = btor_mapped_node (exp_map, BTOR_REAL_ADDR_NODE (real_exp->e[i]));
        assert (exp);
        res->e[i] = BTOR_IS_INVERTED_NODE (real_exp->e[i])
                        ? BTOR_INVALID_NODE (real_exp->e[i])
                        : exp;
      }
    }
    else
    {
      res->symbol = btor_strdup (cmm, real_exp->symbol);
      if (BTOR_IS_ARRAY_EQ_NODE (real_exp))
      {
        exp = btor_mapped_node (exp_map, real_exp->vreads->exp1);
        assert (exp);
        exp2 = btor_mapped_node (exp_map, real_exp->vreads->exp2);
        assert (exp2);
        res->vreads = new_exp_pair (clone, exp, exp2);
      }
    }

    for (i = 0; i < real_exp->arity; i++)
    {
      BTOR_PUSH_STACK (mm, *parents, real_exp->prev_parent[i]);
      BTOR_PUSH_STACK (mm, *parents, real_exp->next_parent[i]);
    }
  }

  if (BTOR_IS_ARRAY_NODE (real_exp))
  {
    BTOR_PUSH_STACK (mm, *parents, real_exp->first_aeg_acond_parent);
    BTOR_PUSH_STACK (mm, *parents, real_exp->last_aeg_acond_parent);

    if (!BTOR_IS_ARRAY_VAR_NODE (real_exp))
    {
      for (i = 0; i < real_exp->arity; i++)
      {
        BTOR_PUSH_STACK (mm, *parents, real_exp->prev_aeq_acond_parent[i]);
        BTOR_PUSH_STACK (mm, *parents, real_exp->next_aeq_acond_parent[i]);
      }
    }
  }
}

static BtorPtrHashTable *
// TODO do all constraints in one go
clone_constraints (Btor *clone, BtorNodeMap *map, BtorPtrHashTable *constrs)
{
  assert (clone);
  assert (map);
  assert (consts);

  BtorPtrHashTable *res;
  BtorPtrhashTableBucket *b;
  BtorNodePtrStack stack, unmark_stack;
  BtorNodePtrPtrStack parents;
  BtorMemMgr *mm;
  BtorNode *cur, *real_cur, *new;

  mm = clone->mm;

  // TODO use existing hash tables
  // res = btor_new_ptr_has_table (mm, (BtorHashPtr) btor_hash_exp_by_id,
  //     (BtorCmpPtr) btor_compare_exp_by_id);

  BTOR_INIT_STACK (stack);
  BTOR_INIT_STACK (unmark_stack);
  BTOR_INIT_STACK (parents);

  for (b = constrs->first; b; b = b->next)
  {
    cur = (BtorNode *) b->key;
    BTOR_PUSH_STACK (mm, stack, cur);
    while (!BTOR_EMPTY_STACK)
    {
      cur      = BTOR_POP_STACK (stack);
      real_cur = BTOR_REAL_ADDR_NODE (cur);
      if (real_cur->clone_mark >= 2) continue;

      if (real_cur->clone_mark == 0)
      {
        real_cur->clone_mark = 1;
        BTOR_PUSH_STACK (mm, stack, cur);
        BTOR_PUSH_STACK (mm, stack, real_cur);
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

        // TODO clone exp
      }

      // real_cur = BTOR_REAL_ADDR_NODE (cur);
      // if (!lookup)
      //  {
      //
      //  }
    }

    /* reset mark flags */
    while (!BTOR_EMPTY_STACK)
    {
      real_cur = BTOR_POP_STACK (unmark_stack);
      assert (BTOR_IS_REGULAR_NODE (real_cur));
      real_cur->mark = 0;
    }

    // TODO reset stacks
  }

  // TODO delete stacks
}

Btor *
btor_clone_btor (Btor *btor)
{
  Btor *clone;
  // BtorMemMgr *mm;
  BtorNodeMap *exp_map, *aig_map, *av_map;

  // mm = btor->mm;
  exp_map = btor_new_node_map (btor);
  aig_map = btor_new_node_map (btor);
  av_map  = btor_new_node_map (btor);

  clone = btor_new_btor ();
  memcpy (&clone->bv_lambda_id,
          &btor->bv_lambda_id,
          (char *) &btor->lod_cache - (char *) &btor->bv_lambda_id);
  memcpy (
      &clone->stats, &btor->stats, btor + sizeof *btor - (char *) &btor->stats);

  // TODO clone top-level constraints
}
