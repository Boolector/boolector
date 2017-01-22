/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2016 Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btorsynth.h"
#include "btorbeta.h"
#include "btorbitvec.h"
#include "btorcore.h"
#include "btormodel.h"
#include "utils/btorhashint.h"
#include "utils/btoriter.h"
#include "utils/btorpartgen.h"
#include "utils/btorstack.h"
#include "utils/btorutil.h"

BTOR_DECLARE_STACK (BtorBitVectorTuplePtr, BtorBitVectorTuple *);
BTOR_DECLARE_STACK (BtorIntHashTablePtr, BtorIntHashTable *);

typedef BtorNode *(*BtorUnOp) (Btor *, BtorNode *);
typedef BtorNode *(*BtorBinOp) (Btor *, BtorNode *, BtorNode *);
typedef BtorNode *(*BtorTerOp) (Btor *, BtorNode *, BtorNode *, BtorNode *);

struct Op
{
  bool assoc;
  uint8_t arity;
  union
  {
    BtorUnOp un;
    BtorBinOp bin;
    BtorTerOp ter;
    void *fun;
  };
  const char *name;
  uint32_t num_added;
};

typedef struct Op Op;

struct Candidates
{
  BtorVoidPtrStack exps;
  BtorIntStack nexps_level;
  uint32_t nnullary;
  uint32_t nunary;
  uint32_t nbinary;
  uint32_t nternary;
  uint32_t nexps;
};

typedef struct Candidates Candidates;

struct BtorCartProdIterator
{
  BtorSortId cur_sort;
  BtorIntHashTable *e0_exps;
  BtorIntHashTable *e1_exps;

  uint32_t e0_cur_pos;
  uint32_t e1_cur_pos;
  BtorNodePtrStack *e0_stack;
  BtorNodePtrStack *e1_stack;

  BtorNode *tuple[2];
};

typedef struct BtorCartProdIterator BtorCartProdIterator;

static void
init_next_sort (BtorCartProdIterator *it)
{
  uint32_t i, key;
  BtorHashTableData *d;

  if (!it->cur_sort)
    i = 0;
  else
  {
    assert (btor_contains_int_hash_table (it->e0_exps, it->cur_sort));
    i = btor_get_pos_int_hash_table (it->e0_exps, it->cur_sort) + 1;
  }

  it->e0_cur_pos = 0;
  it->e1_cur_pos = 0;

  for (; i < it->e0_exps->size; i++)
  {
    key = it->e0_exps->keys[i];
    if (key)
    {
      it->cur_sort = key;

      /* set expression stacks */
      it->e0_stack = it->e0_exps->data[i].as_ptr;

      d = btor_get_int_hash_map (it->e1_exps, key);
      if (d)
        it->e1_stack = d->as_ptr;
      else
        break;
      return;
    }
  }
  it->cur_sort = 0;
}

void
btor_init_cart_prod_iterator (BtorCartProdIterator *it,
                              BtorIntHashTable *e0_exps,
                              BtorIntHashTable *e1_exps)
{
  assert (e0_exps);
  assert (e1_exps);

  it->e0_exps  = e0_exps;
  it->e1_exps  = e1_exps;
  it->cur_sort = 0;
  it->e0_stack = 0;
  it->e1_stack = 0;
  init_next_sort (it);
}

BtorNode **
btor_next_cart_prod_iterator (BtorCartProdIterator *it)
{
  assert (it->e0_stack);
  assert (it->e1_stack);
  assert (it->e0_cur_pos < BTOR_COUNT_STACK (*it->e0_stack));
  assert (it->e1_cur_pos < BTOR_COUNT_STACK (*it->e1_stack));

  it->tuple[1] = BTOR_PEEK_STACK (*it->e1_stack, it->e1_cur_pos);
  it->tuple[0] = BTOR_PEEK_STACK (*it->e0_stack, it->e0_cur_pos);

  if (it->e1_cur_pos < BTOR_COUNT_STACK (*it->e1_stack)) it->e1_cur_pos++;

  if (it->e1_cur_pos >= BTOR_COUNT_STACK (*it->e1_stack))
  {
    it->e1_cur_pos = 0;
    it->e0_cur_pos++;
  }
  if (it->e0_cur_pos >= BTOR_COUNT_STACK (*it->e0_stack)) init_next_sort (it);
  return it->tuple;
}

bool
btor_has_next_cart_prod_iterator (BtorCartProdIterator *it)
{
  return it->cur_sort != 0;
}

/* ------------------------------------------------------------------------- */

static void
collect_exps_post_order (Btor *btor,
                         BtorNode *roots[],
                         uint32_t nroots,
                         BtorIntHashTable *value_in_map,
                         BtorNodePtrStack *exps,
                         BtorNodePtrStack *cone,
                         BtorIntHashTable *cone_hash)
{
  assert (btor);
  assert (roots);
  assert (nroots);
  assert (value_in_map);
  assert (exps);
  assert (cone);

  uint32_t i;
  int32_t j;
  BtorNode *cur, *real_cur, *var = 0;
  BtorNodePtrStack visit;
  BtorIntHashTable *cache;
  BtorHashTableData *d;
  BtorMemMgr *mm;
  BtorNodeIterator it;

  mm    = btor->mm;
  cache = btor_new_int_hash_map (mm);

  /* collect exps to evaluate in post-order */
  BTOR_INIT_STACK (visit);
  for (i = 0; i < nroots; i++) BTOR_PUSH_STACK (mm, visit, roots[i]);
  while (!BTOR_EMPTY_STACK (visit))
  {
    cur      = BTOR_POP_STACK (visit);
    real_cur = BTOR_REAL_ADDR_NODE (cur);

    d = btor_get_int_hash_map (cache, real_cur->id);
    if (!d)
    {
      btor_add_int_hash_map (cache, real_cur->id);
      BTOR_PUSH_STACK (mm, visit, cur);

      /* found variable */
      if (btor_is_param_node (real_cur)
          && (d = btor_get_int_hash_map (value_in_map, real_cur->id))
          && d->as_int == -1)
      {
        assert (!var);
        var = real_cur;
      }

      if (btor_is_apply_node (real_cur)) continue;

      for (j = real_cur->arity - 1; j >= 0; j--)
        BTOR_PUSH_STACK (mm, visit, real_cur->e[j]);
    }
    else if (!d->as_int)
    {
      assert (!btor_is_fun_node (real_cur));
      assert (!btor_is_apply_node (real_cur));
      d->as_int = 1;
      BTOR_PUSH_STACK (mm, *exps, cur);
    }
    else
    {
      BTOR_PUSH_STACK (mm, *exps, cur);
    }
  }

  /* mark cone of variable */
  assert (var);
  BTOR_PUSH_STACK (mm, visit, var);
  while (!BTOR_EMPTY_STACK (visit))
  {
    cur = BTOR_POP_STACK (visit);
    assert (BTOR_IS_REGULAR_NODE (cur));

    if (!btor_contains_int_hash_map (cache, cur->id)
        || btor_contains_int_hash_table (cone_hash, cur->id))
      continue;

    btor_add_int_hash_table (cone_hash, cur->id);
    btor_init_parent_iterator (&it, cur);
    while (btor_has_next_parent_iterator (&it))
      BTOR_PUSH_STACK (mm, visit, btor_next_parent_iterator (&it));
  }

  /* collect exps in cone that need to be evaluated each check */
  for (i = 0; i < nroots; i++)
  {
    cur      = roots[i];
    real_cur = BTOR_REAL_ADDR_NODE (cur);
    if (btor_contains_int_hash_table (cone_hash, real_cur->id))
      BTOR_PUSH_STACK (mm, visit, cur);
  }

  btor_delete_int_hash_map (cache);
  cache = btor_new_int_hash_map (mm);

  while (!BTOR_EMPTY_STACK (visit))
  {
    cur      = BTOR_POP_STACK (visit);
    real_cur = BTOR_REAL_ADDR_NODE (cur);

    if (!btor_contains_int_hash_table (cone_hash, real_cur->id))
    {
      BTOR_PUSH_STACK (mm, *cone, cur);
      continue;
    }

    d = btor_get_int_hash_map (cache, real_cur->id);
    if (!d)
    {
      btor_add_int_hash_map (cache, real_cur->id);
      BTOR_PUSH_STACK (mm, visit, cur);

      if (btor_is_apply_node (real_cur)) continue;

      for (j = real_cur->arity - 1; j >= 0; j--)
        BTOR_PUSH_STACK (mm, visit, real_cur->e[j]);
    }
    else if (!d->as_int)
    {
      assert (!btor_is_fun_node (real_cur));
      assert (!btor_is_apply_node (real_cur));
      d->as_int = 1;
      BTOR_PUSH_STACK (mm, *cone, cur);
    }
    else
    {
      BTOR_PUSH_STACK (mm, *cone, cur);
    }
  }

  BTOR_RELEASE_STACK (mm, visit);
  btor_delete_int_hash_map (cache);
}

static BtorBitVector *
eval_candidate (Btor *btor,
                BtorNode *candidate,
                BtorBitVectorTuple *value_in,
                BtorBitVector *value_out,
                BtorIntHashTable *value_in_map)
{
  assert (btor);
  assert (candidate);
  assert (value_in);
  assert (value_out);
  assert (value_in_map);

  size_t j;
  int32_t i, pos;
  BtorNode *cur, *real_cur;
  BtorNodePtrStack visit;
  BtorIntHashTable *cache;
  BtorHashTableData *d;
  BtorBitVectorPtrStack arg_stack;
  BtorMemMgr *mm;
  BtorBitVector **bv, *result, *inv_result, *a;

  mm    = btor->mm;
  cache = btor_new_int_hash_map (mm);

  BTOR_INIT_STACK (arg_stack);
  BTOR_INIT_STACK (visit);
  BTOR_PUSH_STACK (mm, visit, candidate);
  while (!BTOR_EMPTY_STACK (visit))
  {
    cur      = BTOR_POP_STACK (visit);
    real_cur = BTOR_REAL_ADDR_NODE (cur);

    d = btor_get_int_hash_map (cache, real_cur->id);
    if (!d)
    {
      btor_add_int_hash_map (cache, real_cur->id);
      BTOR_PUSH_STACK (mm, visit, cur);

      if (btor_is_apply_node (real_cur)) continue;

      for (i = real_cur->arity - 1; i >= 0; i--)
        BTOR_PUSH_STACK (mm, visit, real_cur->e[i]);
    }
    else if (!d->as_ptr)
    {
      assert (!btor_is_fun_node (real_cur));
      assert (!btor_is_apply_node (real_cur));

      arg_stack.top -= real_cur->arity;
      bv = arg_stack.top;

      switch (real_cur->kind)
      {
        case BTOR_BV_CONST_NODE:
          result = btor_copy_bv (mm, btor_const_get_bits (real_cur));
          break;

        case BTOR_PARAM_NODE:
        case BTOR_BV_VAR_NODE:
          assert (btor_get_int_hash_map (value_in_map, real_cur->id));
          pos = btor_get_int_hash_map (value_in_map, real_cur->id)->as_int;
          /* initial signature computation */
          if (pos == -1)
          {
            assert (value_out);
            assert (!candidate);
            result = btor_copy_bv (mm, value_out);
            assert (btor_get_exp_width (real_cur->btor, real_cur)
                    == value_out->width);
          }
          else
            result = btor_copy_bv (mm, value_in->bv[pos]);
          break;

        case BTOR_SLICE_NODE:
          result = btor_slice_bv (mm,
                                  bv[0],
                                  btor_slice_get_upper (real_cur),
                                  btor_slice_get_lower (real_cur));
          break;

        case BTOR_AND_NODE: result = btor_and_bv (mm, bv[0], bv[1]); break;

        case BTOR_BV_EQ_NODE: result = btor_eq_bv (mm, bv[0], bv[1]); break;

        case BTOR_ADD_NODE: result = btor_add_bv (mm, bv[0], bv[1]); break;

        case BTOR_MUL_NODE: result = btor_mul_bv (mm, bv[0], bv[1]); break;

        case BTOR_ULT_NODE: result = btor_ult_bv (mm, bv[0], bv[1]); break;

        case BTOR_SLL_NODE: result = btor_sll_bv (mm, bv[0], bv[1]); break;

        case BTOR_SRL_NODE: result = btor_srl_bv (mm, bv[0], bv[1]); break;

        case BTOR_UDIV_NODE: result = btor_udiv_bv (mm, bv[0], bv[1]); break;

        case BTOR_UREM_NODE: result = btor_urem_bv (mm, bv[0], bv[1]); break;

        case BTOR_CONCAT_NODE:
          result = btor_concat_bv (mm, bv[0], bv[1]);
          break;

        case BTOR_EXISTS_NODE:
        case BTOR_FORALL_NODE: result = btor_copy_bv (mm, bv[1]); break;

        default:
          assert (real_cur->kind == BTOR_COND_NODE);
          if (btor_is_true_bv (bv[0]))
            result = btor_copy_bv (mm, bv[1]);
          else
            result = btor_copy_bv (mm, bv[2]);
      }

      for (i = 0; i < real_cur->arity; i++) btor_free_bv (mm, bv[i]);

      d->as_ptr = btor_copy_bv (mm, result);

    EVAL_EXP_PUSH_RESULT:
      if (BTOR_IS_INVERTED_NODE (cur))
      {
        inv_result = btor_not_bv (mm, result);
        btor_free_bv (mm, result);
        result = inv_result;
      }
      BTOR_PUSH_STACK (mm, arg_stack, result);
    }
    else
    {
      result = btor_copy_bv (mm, d->as_ptr);
      goto EVAL_EXP_PUSH_RESULT;
    }
  }

  assert (BTOR_COUNT_STACK (arg_stack) == 1);
  result = BTOR_POP_STACK (arg_stack);

  for (j = 0; j < cache->size; j++)
  {
    a = cache->data[j].as_ptr;
    if (!a) continue;
    btor_free_bv (mm, a);
  }
  BTOR_RELEASE_STACK (mm, visit);
  BTOR_RELEASE_STACK (mm, arg_stack);
  btor_delete_int_hash_map (cache);

  return result;
}

static BtorBitVector *
eval_exps (Btor *btor,
           BtorNode *exps[],
           uint32_t nexps,
           BtorIntHashTable *value_cache,
           BtorIntHashTable *cone_hash,
           BtorNode *candidate,
           BtorBitVectorTuple *value_in,
           BtorBitVector *value_out,
           BtorIntHashTable *value_in_map)
{
  assert (btor);
  assert (exps);
  assert (nexps);

  size_t j;
  uint32_t i, k;
  int32_t pos;
  BtorNode *cur, *real_cur;
  BtorIntHashTable *cache;
  BtorHashTableData *d;
  BtorBitVectorPtrStack arg_stack;
  BtorMemMgr *mm;
  BtorBitVector **bv, *result, *inv_result, *a;

  mm    = btor->mm;
  cache = btor_new_int_hash_map (mm);

  BTOR_INIT_STACK (arg_stack);
  for (i = 0; i < nexps; i++)
  {
    cur      = exps[i];
    real_cur = BTOR_REAL_ADDR_NODE (cur);
    assert (!btor_is_fun_node (real_cur));
    assert (!btor_is_apply_node (real_cur));

    d = btor_get_int_hash_map (cache, real_cur->id);
    if (d)
    {
      result = btor_copy_bv (mm, d->as_ptr);
    }
    else if (cone_hash
             && !btor_contains_int_hash_table (cone_hash, real_cur->id))
    {
      assert (value_cache);
      d = btor_get_int_hash_map (value_cache, real_cur->id);
      assert (d);
      result = btor_copy_bv (mm, d->as_ptr);
    }
    else
    {
      assert (BTOR_COUNT_STACK (arg_stack) >= real_cur->arity);

      arg_stack.top -= real_cur->arity;
      bv = arg_stack.top;

      switch (real_cur->kind)
      {
        case BTOR_BV_CONST_NODE:
          result = btor_copy_bv (mm, btor_const_get_bits (real_cur));
          break;

        case BTOR_PARAM_NODE:
        case BTOR_BV_VAR_NODE:
          assert (btor_get_int_hash_map (value_in_map, real_cur->id));
          pos = btor_get_int_hash_map (value_in_map, real_cur->id)->as_int;
          /* initial signature computation */
          if (pos == -1)
          {
            if (candidate)
            {
              result = eval_candidate (
                  btor, candidate, value_in, value_out, value_in_map);
            }
            else
            {
              assert (value_out);
              result = btor_copy_bv (mm, value_out);
              assert (btor_get_exp_width (real_cur->btor, real_cur)
                      == value_out->width);
            }
          }
          else
            result = btor_copy_bv (mm, value_in->bv[pos]);
          break;

        case BTOR_SLICE_NODE:
          result = btor_slice_bv (mm,
                                  bv[0],
                                  btor_slice_get_upper (real_cur),
                                  btor_slice_get_lower (real_cur));
          break;

        case BTOR_AND_NODE: result = btor_and_bv (mm, bv[0], bv[1]); break;

        case BTOR_BV_EQ_NODE: result = btor_eq_bv (mm, bv[0], bv[1]); break;

        case BTOR_ADD_NODE: result = btor_add_bv (mm, bv[0], bv[1]); break;

        case BTOR_MUL_NODE: result = btor_mul_bv (mm, bv[0], bv[1]); break;

        case BTOR_ULT_NODE: result = btor_ult_bv (mm, bv[0], bv[1]); break;

        case BTOR_SLL_NODE: result = btor_sll_bv (mm, bv[0], bv[1]); break;

        case BTOR_SRL_NODE: result = btor_srl_bv (mm, bv[0], bv[1]); break;

        case BTOR_UDIV_NODE: result = btor_udiv_bv (mm, bv[0], bv[1]); break;

        case BTOR_UREM_NODE: result = btor_urem_bv (mm, bv[0], bv[1]); break;

        case BTOR_CONCAT_NODE:
          result = btor_concat_bv (mm, bv[0], bv[1]);
          break;

        case BTOR_EXISTS_NODE:
        case BTOR_FORALL_NODE: result = btor_copy_bv (mm, bv[1]); break;

        default:
          assert (real_cur->kind == BTOR_COND_NODE);
          if (btor_is_true_bv (bv[0]))
            result = btor_copy_bv (mm, bv[1]);
          else
            result = btor_copy_bv (mm, bv[2]);
      }

      for (k = 0; k < real_cur->arity; k++) btor_free_bv (mm, bv[k]);

      d         = btor_add_int_hash_map (cache, real_cur->id);
      d->as_ptr = btor_copy_bv (mm, result);
      if (!cone_hash)
      {
        assert (value_cache);
        btor_add_int_hash_map (value_cache, real_cur->id)->as_ptr =
            btor_copy_bv (mm, result);
      }
    }
    if (BTOR_IS_INVERTED_NODE (cur))
    {
      inv_result = btor_not_bv (mm, result);
      btor_free_bv (mm, result);
      result = inv_result;
    }
    BTOR_PUSH_STACK (mm, arg_stack, result);
  }

  /* merge results of multiple roots */
  result = BTOR_PEEK_STACK (arg_stack, 0);
  for (i = 1; i < BTOR_COUNT_STACK (arg_stack); i++)
  {
    a      = result;
    result = btor_concat_bv (mm, a, BTOR_PEEK_STACK (arg_stack, i));
    btor_free_bv (mm, a);
    btor_free_bv (mm, BTOR_PEEK_STACK (arg_stack, i));
  }

  for (j = 0; j < cache->size; j++)
  {
    a = cache->data[j].as_ptr;
    if (!a) continue;
    btor_free_bv (mm, a);
  }
  btor_delete_int_hash_map (cache);
  BTOR_RELEASE_STACK (mm, arg_stack);

  return result;
}

/* Add expression 'exp' to expression candidates 'candidates' at level
 * 'exp_size'. */
static void
add_exp (Btor *btor, uint32_t exp_size, Candidates *candidates, BtorNode *exp)
{
  assert (exp_size > 0);
  assert (candidates);

  BtorIntHashTable *sorted_exps;
  BtorHashTableData *d;
  BtorSortId sort;
  BtorNodePtrStack *exps;
  BtorMemMgr *mm;

  mm   = btor->mm;
  sort = BTOR_REAL_ADDR_NODE (exp)->sort_id;

  if (exp_size >= BTOR_COUNT_STACK (candidates->exps))
  {
    sorted_exps = btor_new_int_hash_map (mm);
    BTOR_PUSH_STACK (mm, candidates->exps, sorted_exps);
    assert (exp_size == BTOR_COUNT_STACK (candidates->exps) - 1);
  }
  else
    sorted_exps = BTOR_PEEK_STACK (candidates->exps, exp_size);

  d = btor_get_int_hash_map (sorted_exps, sort);
  if (d)
    exps = d->as_ptr;
  else
  {
    BTOR_CNEW (mm, exps);
    btor_add_int_hash_map (sorted_exps, sort)->as_ptr = exps;
  }
  BTOR_PUSH_STACK (mm, *exps, exp);
  candidates->nexps++;
  switch (BTOR_REAL_ADDR_NODE (exp)->arity)
  {
    case 0: candidates->nnullary++; break;
    case 1: candidates->nunary++; break;
    case 2: candidates->nbinary++; break;
    default:
      assert (BTOR_REAL_ADDR_NODE (exp)->arity == 3);
      candidates->nternary++;
      break;
  }
  if (exp_size >= BTOR_COUNT_STACK (candidates->nexps_level))
    BTOR_PUSH_STACK (mm, candidates->nexps_level, 0);
  candidates->nexps_level.start[exp_size]++;
}

#if 0
static BtorNode *
subst_params (Btor * btor, BtorNode * root, BtorNodeMap * map)
{
  size_t j;
  int32_t i;
  BtorMemMgr *mm;
  BtorNodePtrStack visit, args;
  BtorNode *cur, *real_cur, **e, *result;
  BtorIntHashTable *mark;
  BtorHashTableData *d;

  mm = btor->mm;
  mark = btor_new_int_hash_map (mm);
  BTOR_INIT_STACK (visit);
  BTOR_INIT_STACK (args);

  BTOR_PUSH_STACK (mm, visit, root);
  while (!BTOR_EMPTY_STACK (visit))
    {
      cur = BTOR_POP_STACK (visit);
      real_cur = BTOR_REAL_ADDR_NODE (cur);

      d = btor_get_int_hash_map (mark, real_cur->id);
      if (!d)
        {
          btor_add_int_hash_map (mark, real_cur->id);
          BTOR_PUSH_STACK (mm, visit, cur);
          for (i = real_cur->arity - 1; i >= 0; i--)
            BTOR_PUSH_STACK (mm, visit, real_cur->e[i]);
        }
      else if (!d->as_ptr)
        {
          args.top -= real_cur->arity;
          e = args.top;

          if (real_cur->arity == 0)
            {
              if ((result = btor_mapped_node (map, real_cur)))
                {
                  assert (btor_is_param_node (real_cur));
                  result = btor_copy_exp (btor, result);
                }
              else
                result = btor_copy_exp (btor, real_cur);
            }
          else if (real_cur->arity == 1)
            {
              assert (btor_is_slice_node (real_cur));
              result = btor_slice_exp (btor, e[0],
                                       btor_slice_get_upper (real_cur),
                                       btor_slice_get_lower (real_cur));
            }
          else
            result = btor_create_exp (btor, real_cur->kind, e, real_cur->arity);

          d->as_ptr = btor_copy_exp (btor, result);

          for (i = 0; i < real_cur->arity; i++)
            btor_release_exp (btor, e[i]);
PUSH_RESULT:
          BTOR_PUSH_STACK (mm, args, BTOR_COND_INVERT_NODE (cur, result));
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

  BTOR_RELEASE_STACK (mm, args);
  BTOR_RELEASE_STACK (mm, visit);

  for (j = 0; j < mark->size; j++)
    {
      if (!mark->keys[j]) continue;
      assert (mark->data[j].as_ptr);
      btor_release_exp (btor, mark->data[j].as_ptr);
    }

  btor_delete_int_hash_map (mark);

  return result;
}

static BtorNode *
mk_fun (Btor * btor, BtorNode * params[], uint32_t nparams, BtorNode * body)
{
  uint32_t i;
  BtorNodePtrStack new_params;
  BtorNode *p, *new_p, *new_body, *result;
  BtorMemMgr *mm;
  BtorNodeMap *map;

  mm = btor->mm;
  BTOR_INIT_STACK (new_params);
  map = btor_new_node_map (btor);
  for (i = 0; i < nparams; i++)
    {
      p = params[i];
      new_p = btor_param_exp (btor, btor_get_exp_width (btor, p), 0);
      BTOR_PUSH_STACK (mm, new_params, new_p);
      btor_map_node (map, p, new_p);
    }
  assert (BTOR_COUNT_STACK (new_params) == nparams);

  new_body = subst_params (btor, body, map);
  result = btor_fun_exp (btor, new_params.start, nparams, new_body);
  assert (btor_get_fun_arity (btor, result) == nparams);

  while (!BTOR_EMPTY_STACK (new_params))
    btor_release_exp (btor, BTOR_POP_STACK (new_params));
  BTOR_RELEASE_STACK (mm, new_params);
  btor_release_exp (btor, new_body);
  btor_delete_node_map (map);
//  assert (!BTOR_REAL_ADDR_NODE (result)->parameterized);
  return result;
}
#endif

#if 0
struct BinOp
{
  bool assoc;
  BtorBinOp op;
};

typedef struct BinOp BinOp;
#endif

struct Match
{
  uint32_t level;  // TODO: set level in which exp was created
  uint32_t num_matches;
  BtorBitVector *matches;
  BtorNode *exp;
};

typedef struct Match Match;

static Match *
new_match (BtorMemMgr *mm,
           uint32_t level,
           uint32_t num_matches,
           BtorBitVector *matches,
           BtorNode *exp)
{
  Match *res;

  BTOR_CNEW (mm, res);
  res->level       = level;
  res->num_matches = num_matches;
  res->matches     = matches;
  res->exp         = btor_copy_exp (BTOR_REAL_ADDR_NODE (exp)->btor, exp);
  return res;
}

static uint32_t
hash_match (Match *m)
{
  return btor_hash_bv (m->matches);
}

static int32_t
cmp_match (const Match *m0, const Match *m1)
{
  return btor_compare_bv (m0->matches, m1->matches);
}

#if 0
static int32_t
cmp_sort_match (const void * m0, const void * m1)
{
  const Match *m00 = *(Match **) m0;
  const Match *m11 = *(Match **) m1;

  if (m00->num_matches == m11->num_matches)
    return m00->level - m11->level;
//    return btor_compare_bv (m00->matches, m11->matches);
  return m11->num_matches - m00->num_matches;
}
#endif

static void
delete_match (BtorMemMgr *mm, Match *m)
{
  btor_free_bv (mm, m->matches);
  btor_release_exp (BTOR_REAL_ADDR_NODE (m->exp)->btor, m->exp);
  BTOR_DELETE (mm, m);
}

#if 0
BTOR_DECLARE_STACK (MatchPtr, Match *);

static bool 
find_best_matches (Btor * btor,
                   BtorPtrHashTable * matches, BtorNodePtrStack * results)
{
  bool full_cover = false;
  int32_t j, w, u;
  uint32_t i, cur_rem_bits, min_rem_bits, rem_bits, minpos;
  BtorHashTableIterator it;
  MatchPtrStack stack;
  BtorIntStack used;
  Match *m, *minm;
  BtorMemMgr *mm;
  BtorBitVector *bv, *matchbv, *minbv;

  mm = btor->mm;
  BTOR_INIT_STACK (stack);
  BTOR_INIT_STACK (used);

  btor_init_hash_table_iterator (&it, matches);
  while (btor_has_next_hash_table_iterator (&it))
    {
      m = btor_next_hash_table_iterator (&it);
      BTOR_PUSH_STACK (mm, stack, m);
      BTOR_PUSH_STACK (mm, used, 0);
//      btor_print_bv (m->matches);
    }

#if 0
  printf ("sorted:\n");
  for (i = 0; i < BTOR_COUNT_STACK (stack); i++)
    {
      m = BTOR_PEEK_STACK (stack, i);
      printf ("%u %u ", m->num_matches, m->level);
      btor_print_bv (m->matches);
    }
#endif

  if (!BTOR_EMPTY_STACK (stack))
    {
      qsort (stack.start, BTOR_COUNT_STACK (stack), sizeof (Match *),
             cmp_sort_match);
//  printf ("collect:\n");
      matchbv = 0;
      m = BTOR_PEEK_STACK (stack, 0);
      bv = btor_copy_bv (mm, m->matches);
      w = bv->width;
    //  printf ("more cov match: %u (%u), ", m->num_matches, m->level);
    //  btor_print_bv (m->matches);
      BTOR_PUSH_STACK (mm, *results, btor_copy_exp (btor, m->exp));
      full_cover = btor_is_ones_bv (m->matches);
//      printf ("matches: %u, ", m->num_matches);
//      btor_print_bv (m->matches);

#if 0
      do
        {
          rem_bits = 0;
          for (j = w - 1; j >= 0; j--)
            if (!btor_get_bit_bv (bv, j))
              rem_bits++;

          BTOR_POKE_STACK (used, 0, 1);
          minm = 0;
          min_rem_bits = rem_bits;
          for (i = 1; i < BTOR_COUNT_STACK (stack); i++)
            {
              m = BTOR_PEEK_STACK (stack, i);
              u = BTOR_PEEK_STACK (used, i);
              if (u) continue;

              matchbv = m->matches;
              cur_rem_bits = rem_bits;
              for (j = w - 1; j >= 0; j--)
                {
                  if (!btor_get_bit_bv (bv, j) && btor_get_bit_bv (matchbv, j))
                    cur_rem_bits--;
                }
              if (cur_rem_bits < min_rem_bits)
                {
                  min_rem_bits = cur_rem_bits;
                  minm = m;
                  minpos = i;
    //              printf ("new min; %u\n", min_rem_bits);
                }

              if (cur_rem_bits == 0)
                {
    //              printf ("found full coverage\n");
                  full_cover = true;
                  break;
                }
            }

          if (!minm)
            break;

          for (j = w - 1; j >= 0; j--)
            {
              if (!btor_get_bit_bv (bv, j)
                  && btor_get_bit_bv (minm->matches, j))
                btor_set_bit_bv (bv, j, 1);
            }
    //          printf ("more cov match: %u (%u), ", minm->num_matches, minm->level);
    //          btor_print_bv (minm->matches);
          BTOR_PUSH_STACK (mm, *results, btor_copy_exp (btor, minm->exp));
          BTOR_POKE_STACK (used, minpos, 1);
        }
      while (!full_cover && min_rem_bits > 0);
#endif

      btor_free_bv (mm, bv);
      BTOR_RELEASE_STACK (mm, stack);
      BTOR_RELEASE_STACK (mm, used);
    }
  return full_cover;
}
#endif

static BtorBitVectorTuple *
create_signature_exp (Btor *btor,
                      BtorNode *exp,
                      BtorBitVectorTuple *value_in[],
                      BtorBitVector *value_out[],
                      uint32_t nvalues,
                      BtorIntHashTable *value_in_map)
{
  uint32_t i;
  BtorBitVectorTuple *inputs, *sig;
  BtorBitVector *output, *res;
  BtorMemMgr *mm;

  mm  = btor->mm;
  sig = btor_new_bv_tuple (btor->mm, nvalues);

  for (i = 0; i < nvalues; i++)
  {
    inputs = value_in[i];
    output = value_out[i];
    res    = eval_candidate (btor, exp, inputs, output, value_in_map);
    btor_add_to_bv_tuple (mm, sig, res, i);
    btor_free_bv (mm, res);
  }
  return sig;
}

static bool
check_signature_exps (Btor *btor,
                      BtorNode *exps[],
                      uint32_t nexps,
                      BtorIntHashTable *value_caches[],
                      BtorIntHashTable *cone_hash,
                      BtorNode *exp,
                      BtorBitVectorTuple *value_in[],
                      BtorBitVector *value_out[],
                      uint32_t nvalues,
                      BtorIntHashTable *value_in_map,
                      BtorBitVectorTuple **sig,
                      uint32_t *num_matches,
                      BtorBitVector **matchbv)
{
  bool is_equal = true;
  uint32_t i = 0, nmatches = 0;
  BtorBitVectorTuple *inputs;
  BtorBitVector *output, *res, *bv;
  BtorMemMgr *mm;

  mm = btor->mm;

  if (sig) *sig = btor_new_bv_tuple (mm, nvalues);

  if (matchbv) bv = btor_new_bv (mm, nvalues);

  for (i = 0; i < nvalues; i++)
  {
    inputs = value_in[i];
    output = value_out[i];

    if (nexps)
      res = eval_exps (btor,
                       exps,
                       nexps,
                       value_caches[i],
                       cone_hash,
                       exp,
                       inputs,
                       output,
                       value_in_map);
    else
      res = eval_candidate (btor, exp, inputs, output, value_in_map);

    if (btor_compare_bv (res, output) == 0)
    {
      nmatches++;
      if (matchbv) btor_set_bit_bv (bv, i, 1);
    }
    else if (is_equal)
      is_equal = false;

    if (sig) btor_add_to_bv_tuple (mm, *sig, res, i);
    btor_free_bv (mm, res);
  }
  if (num_matches) *num_matches = nmatches;
  if (matchbv) *matchbv = bv;
  return is_equal;
}

static bool
check_candidate_exps (Btor *btor,
                      BtorNode *exps[],
                      uint32_t nexps,
                      BtorIntHashTable *value_caches[],
                      BtorIntHashTable *cone_hash,
                      uint32_t cur_level,
                      BtorNode *exp,
                      BtorSortId target_sort,
                      BtorBitVectorTuple *value_in[],
                      BtorBitVector *value_out[],
                      uint32_t nvalues,
                      BtorIntHashTable *value_in_map,
                      Candidates *candidates,
                      BtorIntHashTable *cache,
                      BtorPtrHashTable *sigs,
                      BtorPtrHashTable *sigs_exp,
                      BtorPtrHashTable *matches,
                      Op *op)
{
  bool found_candidate = false;
  int32_t id;
  uint32_t num_matches    = 0;
  BtorBitVectorTuple *sig = 0, *sig_exp;
  BtorBitVector *matchbv  = 0;
  BtorMemMgr *mm;
  Match *m;

  id = BTOR_GET_ID_NODE (exp);
  mm = btor->mm;

  if (btor_is_bv_const_node (exp) || btor_contains_int_hash_table (cache, id))
  {
    btor_release_exp (btor, exp);
    return false;
  }

  if (nexps == 0 || BTOR_REAL_ADDR_NODE (exp)->sort_id == target_sort)
  {
    /* check signature for candidate expression (in/out values) */
    sig_exp = create_signature_exp (
        btor, exp, value_in, value_out, nvalues, value_in_map);

    if (btor_get_ptr_hash_table (sigs_exp, sig_exp))
    {
      btor_free_bv_tuple (mm, sig_exp);
      btor_release_exp (btor, exp);
      return false;
    }
    btor_add_ptr_hash_table (sigs_exp, sig_exp);

    /* check signature for candidate expression w.r.t. formula */
    found_candidate = check_signature_exps (btor,
                                            exps,
                                            nexps,
                                            value_caches,
                                            cone_hash,
                                            exp,
                                            value_in,
                                            value_out,
                                            nvalues,
                                            value_in_map,
                                            &sig,
                                            &num_matches,
                                            &matchbv);
  }

  if (sig && btor_get_ptr_hash_table (sigs, sig))
  {
    assert (!found_candidate);
    btor_free_bv_tuple (mm, sig);
    btor_free_bv (mm, matchbv);
    btor_release_exp (btor, exp);
    return false;
  }

  if (num_matches > 0)
  {
    m = new_match (mm, cur_level, num_matches, matchbv, exp);
    if (!btor_get_ptr_hash_table (matches, m))
      btor_add_ptr_hash_table (matches, m);
    else
      delete_match (mm, m);
  }
  else if (matchbv)
    btor_free_bv (mm, matchbv);

  if (sig) btor_add_ptr_hash_table (sigs, sig);
  btor_add_int_hash_table (cache, id);
  if (op) op->num_added++;
  add_exp (btor, cur_level, candidates, exp);
  return found_candidate;
}

static inline void
report_stats (Btor *btor,
              double start,
              uint32_t cur_level,
              uint32_t num_checks,
              Candidates *candidates)
{
  double delta;
  delta = btor_time_stamp () - start;
  BTOR_MSG (btor->msg,
            1,
            "level: %u|%u(%u,%u,%u)|%u, %.2f/s, %.2fs, %.2f MiB",
            cur_level,
            candidates->nexps,
            candidates->nnullary,
            candidates->nbinary,
            candidates->nternary,
            num_checks,
            num_checks / delta,
            delta,
            (float) btor->mm->allocated / 1024 / 1024);
}

static void
report_op_stats (Btor *btor, Op ops[], uint32_t nops)
{
  uint32_t i;
  for (i = 0; i < nops; i++)
    BTOR_MSG (btor->msg, 1, "%s: %u", ops[i].name, ops[i].num_added);
}

#if 0
static void
max_chain_length (BtorPtrHashTable * sigs)
{
  uint32_t i, max_len = 0, cur_len, empty_bucks = 0;
  BtorPtrHashBucket *b;

  for (i = 0; i < sigs->size; i++)
    {
      b = sigs->table[i];
      cur_len = 0;
      if (!b) empty_bucks++; 
      while (b)
        {
          cur_len++;
          if (cur_len > max_len)
            max_len = cur_len;
          b = b->chain;
        }
    }
  printf ("max chain: %u, %u/%u\n", max_len, empty_bucks, sigs->size);
}
#endif

#if 0
static void
add_consts (Btor * btor, uint32_t width, Candidates * candidates,
            BtorIntHashTable * cache)
{
  BtorNode *c;

  c = btor_zero_exp (btor, width);
  if (!btor_contains_int_hash_table (cache, BTOR_GET_ID_NODE (c)))
    {
      btor_add_int_hash_table (cache, BTOR_GET_ID_NODE (c));
      add_exp (btor, 1, candidates, c);
    }
  else
    btor_release_exp (btor, c);

  c = btor_ones_exp (btor, width);
  if (!btor_contains_int_hash_table (cache, BTOR_GET_ID_NODE (c)))
    {
      btor_add_int_hash_table (cache, BTOR_GET_ID_NODE (c));
      add_exp (btor, 1, candidates, c);
    }
  else
    btor_release_exp (btor, c);
}
#endif

#define CHECK_CANDIDATE(exp)                                              \
  {                                                                       \
    found_candidate = check_candidate_exps (btor,                         \
                                            trav_cone.start,              \
                                            BTOR_COUNT_STACK (trav_cone), \
                                            value_caches.start,           \
                                            cone_hash,                    \
                                            cur_level,                    \
                                            exp,                          \
                                            target_sort,                  \
                                            value_in,                     \
                                            value_out,                    \
                                            nvalues,                      \
                                            value_in_map,                 \
                                            &candidates,                  \
                                            cache,                        \
                                            sigs,                         \
                                            sigs_exp,                     \
                                            matches,                      \
                                            &ops[i]);                     \
    num_checks++;                                                         \
    if (num_checks % 10000 == 0)                                          \
      report_stats (btor, start, cur_level, num_checks, &candidates);     \
    if (num_checks % 1000 == 0 && btor_terminate_btor (btor))             \
    {                                                                     \
      BTOR_MSG (btor->msg, 1, "terminate");                               \
      goto DONE;                                                          \
    }                                                                     \
    if (found_candidate || num_checks >= max_checks) goto DONE;           \
  }

static BtorNode *
synthesize (Btor *btor,
            BtorNode *inputs[],
            uint32_t ninputs,
            BtorBitVectorTuple *value_in[],
            BtorBitVector *value_out[],
            uint32_t nvalues,
            Op ops[],
            uint32_t nops,
            BtorNode *consts[],
            uint32_t nconsts,
            BtorNode *constraints[],
            uint32_t nconstraints,
            BtorIntHashTable *value_in_map,
            uint32_t max_checks,
            uint32_t max_level,
            BtorNode *prev_synth)
{
  assert (btor);
  assert (inputs);
  assert (ninputs > 0);
  assert (value_in);
  assert (value_out);
  assert (nvalues > 0);
  assert (ops);
  assert (nops > 0);
  assert (!nconsts || consts);

  double start;
  bool found_candidate = false, equal;
  uint32_t i, j, k, *tuple, cur_level = 1, num_checks = 0, num_added;
  BtorNode *exp, **exp_tuple, *result = 0;
  BtorNodePtrStack *exps, trav_exps, trav_cone;
  Candidates candidates;
  BtorIntHashTable *cache, *e0_exps, *e1_exps, *e2_exps;
  BtorPtrHashTable *matches, *sigs, *sigs_exp;
  BtorHashTableData *d;
  BtorMemMgr *mm;
  BtorPartitionGenerator pg;
  BtorCartProdIterator cpit;
  BtorHashTableIterator it;
  BtorSortId bool_sort, target_sort;
  BtorBitVectorPtrStack sig_constraints;
  BtorBitVector *bv, **tmp_value_out;
  BtorIntHashTable *value_cache, *cone_hash;
  BtorIntHashTablePtrStack value_caches;

  start     = btor_time_stamp ();
  mm        = btor->mm;
  bool_sort = btor_bool_sort (&btor->sorts_unique_table);
  cache     = btor_new_int_hash_table (mm);
  cone_hash = btor_new_int_hash_table (mm);
  matches   = btor_new_ptr_hash_table (
      mm, (BtorHashPtr) hash_match, (BtorCmpPtr) cmp_match);
  sigs = btor_new_ptr_hash_table (
      mm, (BtorHashPtr) btor_hash_bv_tuple, (BtorCmpPtr) btor_compare_bv_tuple);
  sigs_exp = btor_new_ptr_hash_table (
      mm, (BtorHashPtr) btor_hash_bv_tuple, (BtorCmpPtr) btor_compare_bv_tuple);

  BTOR_INIT_STACK (sig_constraints);
  BTOR_INIT_STACK (trav_exps);
  BTOR_INIT_STACK (trav_cone);
  BTOR_INIT_STACK (value_caches);

  memset (&candidates, 0, sizeof (Candidates));
  BTOR_INIT_STACK (candidates.exps);
  BTOR_PUSH_STACK (mm, candidates.exps, 0);
  BTOR_PUSH_STACK (mm, candidates.nexps_level, 0);

  target_sort =
      btor_bitvec_sort (&btor->sorts_unique_table, value_out[0]->width);

  /* generate target signature */
  tmp_value_out = value_out;
  if (nconstraints > 0)
  {
    /* collect expressions in constraints in post-order for faster
     * evaluations */
    collect_exps_post_order (btor,
                             constraints,
                             nconstraints,
                             value_in_map,
                             &trav_exps,
                             &trav_cone,
                             cone_hash);

    for (i = 0; i < nvalues; i++)
    {
      value_cache = btor_new_int_hash_map (mm);
      bv          = eval_exps (btor,
                      trav_exps.start,
                      BTOR_COUNT_STACK (trav_exps),
                      value_cache,
                      0,
                      0,
                      value_in[i],
                      value_out[i],
                      value_in_map);
      assert (btor_get_opt (btor, BTOR_OPT_EF_SYNTH) != BTOR_EF_SYNTH_ELMR
              || btor_is_ones_bv (bv));
      BTOR_PUSH_STACK (mm, sig_constraints, bv);
      BTOR_PUSH_STACK (mm, value_caches, value_cache);
    }
    value_out = sig_constraints.start;
    assert (nvalues == BTOR_COUNT_STACK (sig_constraints));
    assert (nvalues == BTOR_COUNT_STACK (value_caches));
  }

  if (prev_synth)
  {
#if 0
      exp = prev_synth;
      found_candidate =
        check_signature_exps (btor,
                              trav_cone.start, BTOR_COUNT_STACK (trav_cone),
                              value_caches.start, cone_hash,
                              exp, value_in, value_out, nvalues, value_in_map,
                              0, 0, 0);
#else
    exp             = btor_copy_exp (btor, prev_synth);
    found_candidate = check_candidate_exps (btor,
                                            trav_cone.start,
                                            BTOR_COUNT_STACK (trav_cone),
                                            value_caches.start,
                                            cone_hash,
                                            cur_level,
                                            exp,
                                            target_sort,
                                            value_in,
                                            value_out,
                                            nvalues,
                                            value_in_map,
                                            &candidates,
                                            cache,
                                            sigs,
                                            sigs_exp,
                                            matches,
                                            0);
#endif
    num_checks++;
    if (num_checks % 10000 == 0)
      report_stats (btor, start, cur_level, num_checks, &candidates);
    if (found_candidate)
    {
      BTOR_MSG (btor->msg, 1, "previously synthesized term matches");
      goto DONE;
    }
  }

  /* level 1 checks (inputs) */
  for (i = 0; i < ninputs; i++)
  {
    exp             = btor_copy_exp (btor, inputs[i]);
    found_candidate = check_candidate_exps (btor,
                                            trav_cone.start,
                                            BTOR_COUNT_STACK (trav_cone),
                                            value_caches.start,
                                            cone_hash,
                                            cur_level,
                                            exp,
                                            target_sort,
                                            value_in,
                                            value_out,
                                            nvalues,
                                            value_in_map,
                                            &candidates,
                                            cache,
                                            sigs,
                                            sigs_exp,
                                            matches,
                                            0);
    num_checks++;
    if (num_checks % 10000 == 0)
      report_stats (btor, start, cur_level, num_checks, &candidates);
    if (found_candidate) goto DONE;
  }

  /* check for constant function */
  equal = true;
  for (i = 1; i < nvalues; i++)
  {
    if (btor_compare_bv (tmp_value_out[i - 1], tmp_value_out[i]))
    {
      equal = false;
      break;
    }
  }
  if (equal)
  {
    found_candidate = true;
    exp             = btor_const_exp (btor, tmp_value_out[0]);
    add_exp (btor, 1, &candidates, exp);
    goto DONE;
  }

  /* add constants to level 1 */
  for (i = 0; i < nconsts; i++)
    add_exp (btor, 1, &candidates, btor_copy_exp (btor, consts[i]));

#if 0
  /* add the desired outputs as constants to level 1 */
  for (i = 0; i < nvalues; i++)
    {
      exp = btor_const_exp (btor, tmp_value_out[i]);
      add_exp (btor, 1, &candidates, exp);
    }
#endif

  /* level 2+ checks */
  for (cur_level = 2; !max_level || cur_level < max_level; cur_level++)
  {
    /* initialize current level */
    BTOR_PUSH_STACK (mm, candidates.exps, btor_new_int_hash_map (mm));
    assert (cur_level == BTOR_COUNT_STACK (candidates.exps) - 1);
    report_stats (btor, start, cur_level, num_checks, &candidates);

    num_added = candidates.nexps;
    for (i = 0; i < nops; i++)
    {
      if (ops[i].arity == 1)
      {
        /* use all expressions from previous level and apply unary
         * operators */
        e0_exps = BTOR_PEEK_STACK (candidates.exps, cur_level - 1);
        for (j = 0; j < e0_exps->size; j++)
        {
          if (!e0_exps->keys[j]) continue;
          exps = e0_exps->data[j].as_ptr;
          for (k = 0; k < BTOR_COUNT_STACK (*exps); k++)
          {
            exp = ops[i].un (btor, BTOR_PEEK_STACK (*exps, k));
            CHECK_CANDIDATE (exp);
          }
        }
      }
      else if (ops[i].arity == 2)
      {
        btor_init_part_gen (&pg, cur_level, 2, !ops[i].assoc);
        while (btor_has_next_part_gen (&pg))
        {
          tuple   = btor_next_part_gen (&pg);
          e0_exps = BTOR_PEEK_STACK (candidates.exps, tuple[0]);
          e1_exps = BTOR_PEEK_STACK (candidates.exps, tuple[1]);

          btor_init_cart_prod_iterator (&cpit, e0_exps, e1_exps);
          while (btor_has_next_cart_prod_iterator (&cpit))
          {
            exp_tuple = btor_next_cart_prod_iterator (&cpit);
            exp       = ops[i].bin (btor, exp_tuple[0], exp_tuple[1]);
            CHECK_CANDIDATE (exp);
          }
        }
      }
      else if (cur_level > 2)
      {
        assert (ops[i].arity == 3);

        btor_init_part_gen (&pg, cur_level, 3, true);
        while (btor_has_next_part_gen (&pg))
        {
          tuple   = btor_next_part_gen (&pg);
          e0_exps = BTOR_PEEK_STACK (candidates.exps, tuple[0]);
          e1_exps = BTOR_PEEK_STACK (candidates.exps, tuple[1]);
          e2_exps = BTOR_PEEK_STACK (candidates.exps, tuple[2]);

          /* no bool expression in level 'tuple[0]' */
          d = btor_get_int_hash_map (e0_exps, bool_sort);
          if (!d) continue;

          exps = d->as_ptr;
          btor_init_cart_prod_iterator (&cpit, e1_exps, e2_exps);
          while (btor_has_next_cart_prod_iterator (&cpit))
          {
            exp_tuple = btor_next_cart_prod_iterator (&cpit);

            for (j = 0; j < BTOR_COUNT_STACK (*exps); j++)
            {
              exp = ops[i].ter (
                  btor, BTOR_PEEK_STACK (*exps, j), exp_tuple[0], exp_tuple[1]);
              CHECK_CANDIDATE (exp);
            }
          }
        }
      }
    }
    report_op_stats (btor, ops, nops);
    /* no more expressions generated */
    if (num_added == candidates.nexps) break;
  }
DONE:
  report_stats (btor, start, cur_level, num_checks, &candidates);
  report_op_stats (btor, ops, nops);

  if (found_candidate)
    result = btor_copy_exp (btor, exp);
  else
  {
    equal = true;
    for (i = 1; i < nvalues; i++)
    {
      if (btor_compare_bv (tmp_value_out[i - 1], tmp_value_out[i]))
      {
        equal = false;
        break;
      }
    }
    if (equal)
    {
      found_candidate = true;
      result          = btor_const_exp (btor, tmp_value_out[0]);
    }
  }

  if (found_candidate)
    BTOR_MSG (btor->msg,
              1,
              "found candidate after enumerating %u expressions",
              num_checks);
  else
    BTOR_MSG (btor->msg, 1, "no candidate found");

  /* cleanup */
  for (i = 1; i < BTOR_COUNT_STACK (candidates.exps); i++)
  {
    e0_exps = BTOR_PEEK_STACK (candidates.exps, i);
    for (j = 0; j < e0_exps->size; j++)
    {
      if (!e0_exps->data[j].as_ptr) continue;
      exps = e0_exps->data[j].as_ptr;
      while (!BTOR_EMPTY_STACK (*exps))
        btor_release_exp (btor, BTOR_POP_STACK (*exps));
      BTOR_RELEASE_STACK (mm, *exps);
      BTOR_DELETE (mm, exps);
    }
    btor_delete_int_hash_map (e0_exps);
  }
  BTOR_RELEASE_STACK (mm, candidates.exps);
  BTOR_RELEASE_STACK (mm, candidates.nexps_level);

  while (!BTOR_EMPTY_STACK (value_caches))
  {
    value_cache = BTOR_POP_STACK (value_caches);
    for (j = 0; j < value_cache->size; j++)
    {
      if (!value_cache->data[j].as_ptr) continue;
      btor_free_bv (mm, value_cache->data[j].as_ptr);
    }
    btor_delete_int_hash_map (value_cache);
  }
  BTOR_RELEASE_STACK (mm, value_caches);

  while (!BTOR_EMPTY_STACK (sig_constraints))
    btor_free_bv (mm, BTOR_POP_STACK (sig_constraints));
  BTOR_RELEASE_STACK (mm, sig_constraints);

  btor_init_hash_table_iterator (&it, matches);
  while (btor_has_next_hash_table_iterator (&it))
    delete_match (mm, btor_next_hash_table_iterator (&it));

  btor_init_hash_table_iterator (&it, sigs);
  btor_queue_hash_table_iterator (&it, sigs_exp);
  while (btor_has_next_hash_table_iterator (&it))
    btor_free_bv_tuple (mm, btor_next_hash_table_iterator (&it));

  btor_delete_ptr_hash_table (sigs);
  btor_delete_ptr_hash_table (sigs_exp);
  btor_delete_ptr_hash_table (matches);
  btor_delete_int_hash_table (cache);
  BTOR_RELEASE_STACK (mm, trav_exps);
  BTOR_RELEASE_STACK (mm, trav_cone);

  assert (!result || BTOR_REAL_ADDR_NODE (result)->sort_id == target_sort);
  btor_release_sort (&btor->sorts_unique_table, bool_sort);
  btor_release_sort (&btor->sorts_unique_table, target_sort);
  return result;
}

#define INIT_OP(ARITY, ASSOC, FPTR) \
  {                                 \
    ops[i].arity     = ARITY;       \
    ops[i].assoc     = ASSOC;       \
    ops[i].fun       = FPTR;        \
    ops[i].num_added = 0;           \
    ops[i].name      = #FPTR;       \
    i += 1;                         \
  }

static uint32_t
init_ops (Btor *btor, Op *ops)
{
  uint32_t i = 0;

  INIT_OP (1, false, btor_not_exp);
  //  INIT_OP (1, false, btor_neg_exp);
  //  INIT_OP (1, false, btor_redor_exp);
  //  INIT_OP (1, false, btor_redxor_exp);
  //  INIT_OP (1, false, btor_redand_exp);
  //  INIT_OP (1, false, btor_inc_exp);
  //  INIT_OP (1, false, btor_dec_exp);

  /* boolean ops */
  INIT_OP (2, false, btor_ult_exp);
  INIT_OP (2, false, btor_slt_exp);
  INIT_OP (2, true, btor_eq_exp);

  /* bv ops */
  if (btor->ops[BTOR_AND_NODE].cur > 0) INIT_OP (2, true, btor_and_exp);
  if (btor->ops[BTOR_ADD_NODE].cur > 0)
  {
    INIT_OP (2, true, btor_add_exp);
    INIT_OP (2, false, btor_sub_exp);
  }
  if (btor->ops[BTOR_MUL_NODE].cur > 0) INIT_OP (2, true, btor_mul_exp);
  if (btor->ops[BTOR_UDIV_NODE].cur > 0)
  {
    INIT_OP (2, false, btor_udiv_exp);
    INIT_OP (2, false, btor_sdiv_exp);
  }
  if (btor->ops[BTOR_UREM_NODE].cur > 0)
  {
    INIT_OP (2, false, btor_urem_exp);
    INIT_OP (2, false, btor_srem_exp);
    INIT_OP (2, false, btor_smod_exp);
  }
#if 0
  INIT_OP (2, true,  btor_ne_exp);
  INIT_OP (2, true,  btor_xor_exp);
  INIT_OP (2, true,  btor_xnor_exp);
  INIT_OP (2, true,  btor_nand_exp);
  INIT_OP (2, true,  btor_or_exp);
  INIT_OP (2, true,  btor_nor_exp);
  /* additonal operations */
  INIT_OP (2, true, btor_uaddo_exp);
  INIT_OP (2, true, btor_saddo_exp);
  INIT_OP (2, true, btor_umulo_exp);
  INIT_OP (2, true, btor_smulo_exp);
  INIT_OP (2, false, btor_slt_exp);
  INIT_OP (2, false, btor_ugt_exp);
  INIT_OP (2, false, btor_sgt_exp);
  INIT_OP (2, false, btor_ugte_exp);
  INIT_OP (2, false, btor_sgte_exp);
  INIT_OP (2, false, btor_sub_exp);
  INIT_OP (2, false, btor_usubo_exp);
  INIT_OP (2, false, btor_ssubo_exp);
  INIT_OP (2, false, btor_udiv_exp);
  INIT_OP (2, false, btor_sdiv_exp);
  INIT_OP (2, false, btor_sdivo_exp);
  INIT_OP (2, false, btor_urem_exp);
  INIT_OP (2, false, btor_srem_exp);
  INIT_OP (2, false, btor_smod_exp);
  INIT_OP (2, false, btor_concat_exp);
#endif
  INIT_OP (3, false, btor_cond_exp);
  return i;
}

BtorNode *
btor_synthesize_term (Btor *btor,
                      BtorNode *params[],
                      uint32_t nparams,
                      BtorBitVectorTuple *value_in[],
                      BtorBitVector *value_out[],
                      uint32_t nvalues,
                      BtorIntHashTable *value_in_map,
                      BtorNode *constraints[],
                      uint32_t nconstraints,
                      BtorNode *consts[],
                      uint32_t nconsts,
                      uint32_t max_checks,
                      uint32_t max_level,
                      BtorNode *prev_synth)
{
  uint32_t nops;
  Op ops[64];
  BtorNode *result;

  nops = init_ops (btor, ops);
  assert (nops);

  result = synthesize (btor,
                       params,
                       nparams,
                       value_in,
                       value_out,
                       nvalues,
                       ops,
                       nops,
                       consts,
                       nconsts,
                       constraints,
                       nconstraints,
                       value_in_map,
                       max_checks,
                       max_level,
                       prev_synth);

  return result;
}
