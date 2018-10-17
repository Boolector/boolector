/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2016-2017 Mathias Preiner.
 *  Copyright (C) 2017 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btorsynth.h"
#include "btorbeta.h"
#include "btorbv.h"
#include "btorcore.h"
#include "btormodel.h"
#include "utils/btorhashint.h"
#include "utils/btornodeiter.h"
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
    assert (btor_hashint_table_contains (it->e0_exps, it->cur_sort));
    i = btor_hashint_table_get_pos (it->e0_exps, it->cur_sort) + 1;
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

      d = btor_hashint_map_get (it->e1_exps, key);
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
  cache = btor_hashint_map_new (mm);

  /* collect exps to evaluate in post-order */
  BTOR_INIT_STACK (mm, visit);
  for (i = 0; i < nroots; i++) BTOR_PUSH_STACK (visit, roots[i]);
  while (!BTOR_EMPTY_STACK (visit))
  {
    cur      = BTOR_POP_STACK (visit);
    real_cur = btor_node_real_addr (cur);

    d = btor_hashint_map_get (cache, real_cur->id);
    if (!d)
    {
      btor_hashint_map_add (cache, real_cur->id);
      BTOR_PUSH_STACK (visit, cur);

      /* found variable */
      if (btor_node_is_param (real_cur)
          && (d = btor_hashint_map_get (value_in_map, real_cur->id))
          && d->as_int == -1)
      {
        assert (!var);
        var = real_cur;
      }

      if (btor_node_is_apply (real_cur)) continue;

      for (j = real_cur->arity - 1; j >= 0; j--)
        BTOR_PUSH_STACK (visit, real_cur->e[j]);
    }
    else if (!d->as_int)
    {
      assert (!btor_node_is_fun (real_cur));
      assert (!btor_node_is_apply (real_cur));
      d->as_int = 1;
      BTOR_PUSH_STACK (*exps, cur);
    }
    else
    {
      BTOR_PUSH_STACK (*exps, cur);
    }
  }

  /* mark cone of variable */
  assert (var);
  BTOR_PUSH_STACK (visit, var);
  while (!BTOR_EMPTY_STACK (visit))
  {
    cur = BTOR_POP_STACK (visit);
    assert (btor_node_is_regular (cur));

    if (!btor_hashint_map_contains (cache, cur->id)
        || btor_hashint_table_contains (cone_hash, cur->id))
      continue;

    btor_hashint_table_add (cone_hash, cur->id);
    btor_iter_parent_init (&it, cur);
    while (btor_iter_parent_has_next (&it))
      BTOR_PUSH_STACK (visit, btor_iter_parent_next (&it));
  }

  /* collect exps in cone that need to be evaluated each check */
  for (i = 0; i < nroots; i++)
  {
    cur      = roots[i];
    real_cur = btor_node_real_addr (cur);
    if (btor_hashint_table_contains (cone_hash, real_cur->id))
      BTOR_PUSH_STACK (visit, cur);
  }

  btor_hashint_map_delete (cache);
  cache = btor_hashint_map_new (mm);

  while (!BTOR_EMPTY_STACK (visit))
  {
    cur      = BTOR_POP_STACK (visit);
    real_cur = btor_node_real_addr (cur);

    if (!btor_hashint_table_contains (cone_hash, real_cur->id))
    {
      BTOR_PUSH_STACK (*cone, cur);
      continue;
    }

    d = btor_hashint_map_get (cache, real_cur->id);
    if (!d)
    {
      btor_hashint_map_add (cache, real_cur->id);
      BTOR_PUSH_STACK (visit, cur);

      if (btor_node_is_apply (real_cur)) continue;

      for (j = real_cur->arity - 1; j >= 0; j--)
        BTOR_PUSH_STACK (visit, real_cur->e[j]);
    }
    else if (!d->as_int)
    {
      assert (!btor_node_is_fun (real_cur));
      assert (!btor_node_is_apply (real_cur));
      d->as_int = 1;
      BTOR_PUSH_STACK (*cone, cur);
    }
    else
    {
      BTOR_PUSH_STACK (*cone, cur);
    }
  }

  BTOR_RELEASE_STACK (visit);
  btor_hashint_map_delete (cache);
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
  cache = btor_hashint_map_new (mm);

  BTOR_INIT_STACK (mm, arg_stack);
  BTOR_INIT_STACK (mm, visit);
  BTOR_PUSH_STACK (visit, candidate);
  while (!BTOR_EMPTY_STACK (visit))
  {
    cur      = BTOR_POP_STACK (visit);
    real_cur = btor_node_real_addr (cur);

    d = btor_hashint_map_get (cache, real_cur->id);
    if (!d)
    {
      btor_hashint_map_add (cache, real_cur->id);
      BTOR_PUSH_STACK (visit, cur);

      if (btor_node_is_apply (real_cur)) continue;

      for (i = real_cur->arity - 1; i >= 0; i--)
        BTOR_PUSH_STACK (visit, real_cur->e[i]);
    }
    else if (!d->as_ptr)
    {
      assert (!btor_node_is_fun (real_cur));
      assert (!btor_node_is_apply (real_cur));

      arg_stack.top -= real_cur->arity;
      bv = arg_stack.top;

      switch (real_cur->kind)
      {
        case BTOR_CONST_NODE:
          result = btor_bv_copy (mm, btor_node_bv_const_get_bits (real_cur));
          break;

        case BTOR_PARAM_NODE:
        case BTOR_VAR_NODE:
          assert (btor_hashint_map_get (value_in_map, real_cur->id));
          pos = btor_hashint_map_get (value_in_map, real_cur->id)->as_int;
          /* initial signature computation */
          if (pos == -1)
          {
            assert (value_out);
            assert (!candidate);
            result = btor_bv_copy (mm, value_out);
            assert (btor_node_bv_get_width (real_cur->btor, real_cur)
                    == value_out->width);
          }
          else
            result = btor_bv_copy (mm, value_in->bv[pos]);
          break;

        case BTOR_BV_SLICE_NODE:
          result = btor_bv_slice (mm,
                                  bv[0],
                                  btor_node_bv_slice_get_upper (real_cur),
                                  btor_node_bv_slice_get_lower (real_cur));
          break;

        case BTOR_BV_AND_NODE: result = btor_bv_and (mm, bv[0], bv[1]); break;

        case BTOR_BV_EQ_NODE: result = btor_bv_eq (mm, bv[0], bv[1]); break;

        case BTOR_BV_ADD_NODE: result = btor_bv_add (mm, bv[0], bv[1]); break;

        case BTOR_BV_MUL_NODE: result = btor_bv_mul (mm, bv[0], bv[1]); break;

        case BTOR_BV_ULT_NODE: result = btor_bv_ult (mm, bv[0], bv[1]); break;

        case BTOR_BV_SLL_NODE: result = btor_bv_sll (mm, bv[0], bv[1]); break;

        case BTOR_BV_SRL_NODE: result = btor_bv_srl (mm, bv[0], bv[1]); break;

        case BTOR_BV_UDIV_NODE: result = btor_bv_udiv (mm, bv[0], bv[1]); break;

        case BTOR_BV_UREM_NODE: result = btor_bv_urem (mm, bv[0], bv[1]); break;

        case BTOR_BV_CONCAT_NODE:
          result = btor_bv_concat (mm, bv[0], bv[1]);
          break;

        case BTOR_EXISTS_NODE:
        case BTOR_FORALL_NODE: result = btor_bv_copy (mm, bv[1]); break;

        default:
          assert (real_cur->kind == BTOR_COND_NODE);
          if (btor_bv_is_true (bv[0]))
            result = btor_bv_copy (mm, bv[1]);
          else
            result = btor_bv_copy (mm, bv[2]);
      }

      for (i = 0; i < real_cur->arity; i++) btor_bv_free (mm, bv[i]);

      d->as_ptr = btor_bv_copy (mm, result);

    EVAL_EXP_PUSH_RESULT:
      if (btor_node_is_inverted (cur))
      {
        inv_result = btor_bv_not (mm, result);
        btor_bv_free (mm, result);
        result = inv_result;
      }
      BTOR_PUSH_STACK (arg_stack, result);
    }
    else
    {
      result = btor_bv_copy (mm, d->as_ptr);
      goto EVAL_EXP_PUSH_RESULT;
    }
  }

  assert (BTOR_COUNT_STACK (arg_stack) == 1);
  result = BTOR_POP_STACK (arg_stack);

  for (j = 0; j < cache->size; j++)
  {
    a = cache->data[j].as_ptr;
    if (!a) continue;
    btor_bv_free (mm, a);
  }
  BTOR_RELEASE_STACK (visit);
  BTOR_RELEASE_STACK (arg_stack);
  btor_hashint_map_delete (cache);

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
  cache = btor_hashint_map_new (mm);

  BTOR_INIT_STACK (mm, arg_stack);
  for (i = 0; i < nexps; i++)
  {
    cur      = exps[i];
    real_cur = btor_node_real_addr (cur);
    assert (!btor_node_is_fun (real_cur));
    assert (!btor_node_is_apply (real_cur));

    d = btor_hashint_map_get (cache, real_cur->id);
    if (d)
    {
      result = btor_bv_copy (mm, d->as_ptr);
    }
    else if (cone_hash
             && !btor_hashint_table_contains (cone_hash, real_cur->id))
    {
      assert (value_cache);
      d = btor_hashint_map_get (value_cache, real_cur->id);
      assert (d);
      result = btor_bv_copy (mm, d->as_ptr);
    }
    else
    {
      assert (BTOR_COUNT_STACK (arg_stack) >= real_cur->arity);

      arg_stack.top -= real_cur->arity;
      bv = arg_stack.top;

      switch (real_cur->kind)
      {
        case BTOR_CONST_NODE:
          result = btor_bv_copy (mm, btor_node_bv_const_get_bits (real_cur));
          break;

        case BTOR_PARAM_NODE:
        case BTOR_VAR_NODE:
          assert (btor_hashint_map_get (value_in_map, real_cur->id));
          pos = btor_hashint_map_get (value_in_map, real_cur->id)->as_int;
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
              result = btor_bv_copy (mm, value_out);
              assert (btor_node_bv_get_width (real_cur->btor, real_cur)
                      == value_out->width);
            }
          }
          else
            result = btor_bv_copy (mm, value_in->bv[pos]);
          break;

        case BTOR_BV_SLICE_NODE:
          result = btor_bv_slice (mm,
                                  bv[0],
                                  btor_node_bv_slice_get_upper (real_cur),
                                  btor_node_bv_slice_get_lower (real_cur));
          break;

        case BTOR_BV_AND_NODE: result = btor_bv_and (mm, bv[0], bv[1]); break;

        case BTOR_BV_EQ_NODE: result = btor_bv_eq (mm, bv[0], bv[1]); break;

        case BTOR_BV_ADD_NODE: result = btor_bv_add (mm, bv[0], bv[1]); break;

        case BTOR_BV_MUL_NODE: result = btor_bv_mul (mm, bv[0], bv[1]); break;

        case BTOR_BV_ULT_NODE: result = btor_bv_ult (mm, bv[0], bv[1]); break;

        case BTOR_BV_SLL_NODE: result = btor_bv_sll (mm, bv[0], bv[1]); break;

        case BTOR_BV_SRL_NODE: result = btor_bv_srl (mm, bv[0], bv[1]); break;

        case BTOR_BV_UDIV_NODE: result = btor_bv_udiv (mm, bv[0], bv[1]); break;

        case BTOR_BV_UREM_NODE: result = btor_bv_urem (mm, bv[0], bv[1]); break;

        case BTOR_BV_CONCAT_NODE:
          result = btor_bv_concat (mm, bv[0], bv[1]);
          break;

        case BTOR_EXISTS_NODE:
        case BTOR_FORALL_NODE: result = btor_bv_copy (mm, bv[1]); break;

        default:
          assert (real_cur->kind == BTOR_COND_NODE);
          if (btor_bv_is_true (bv[0]))
            result = btor_bv_copy (mm, bv[1]);
          else
            result = btor_bv_copy (mm, bv[2]);
      }

      for (k = 0; k < real_cur->arity; k++) btor_bv_free (mm, bv[k]);

      d         = btor_hashint_map_add (cache, real_cur->id);
      d->as_ptr = btor_bv_copy (mm, result);
      if (!cone_hash)
      {
        assert (value_cache);
        btor_hashint_map_add (value_cache, real_cur->id)->as_ptr =
            btor_bv_copy (mm, result);
      }
    }
    if (btor_node_is_inverted (cur))
    {
      inv_result = btor_bv_not (mm, result);
      btor_bv_free (mm, result);
      result = inv_result;
    }
    BTOR_PUSH_STACK (arg_stack, result);
  }

  /* merge results of multiple roots */
  result = BTOR_PEEK_STACK (arg_stack, 0);
  for (i = 1; i < BTOR_COUNT_STACK (arg_stack); i++)
  {
    a      = result;
    result = btor_bv_concat (mm, a, BTOR_PEEK_STACK (arg_stack, i));
    btor_bv_free (mm, a);
    btor_bv_free (mm, BTOR_PEEK_STACK (arg_stack, i));
  }

  for (j = 0; j < cache->size; j++)
  {
    a = cache->data[j].as_ptr;
    if (!a) continue;
    btor_bv_free (mm, a);
  }
  btor_hashint_map_delete (cache);
  BTOR_RELEASE_STACK (arg_stack);

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
  sort = btor_node_real_addr (exp)->sort_id;

  if (exp_size >= BTOR_COUNT_STACK (candidates->exps))
  {
    sorted_exps = btor_hashint_map_new (mm);
    BTOR_PUSH_STACK (candidates->exps, sorted_exps);
    assert (exp_size == BTOR_COUNT_STACK (candidates->exps) - 1);
  }
  else
    sorted_exps = BTOR_PEEK_STACK (candidates->exps, exp_size);

  d = btor_hashint_map_get (sorted_exps, sort);
  if (d)
    exps = d->as_ptr;
  else
  {
    BTOR_CNEW (mm, exps);
    BTOR_INIT_STACK (mm, *exps);
    btor_hashint_map_add (sorted_exps, sort)->as_ptr = exps;
  }
  BTOR_PUSH_STACK (*exps, exp);
  candidates->nexps++;
  switch (btor_node_real_addr (exp)->arity)
  {
    case 0: candidates->nnullary++; break;
    case 1: candidates->nunary++; break;
    case 2: candidates->nbinary++; break;
    default:
      assert (btor_node_real_addr (exp)->arity == 3);
      candidates->nternary++;
      break;
  }
  if (exp_size >= BTOR_COUNT_STACK (candidates->nexps_level))
    BTOR_PUSH_STACK (candidates->nexps_level, 0);
  candidates->nexps_level.start[exp_size]++;
}

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
  sig = btor_bv_new_tuple (btor->mm, nvalues);

  for (i = 0; i < nvalues; i++)
  {
    inputs = value_in[i];
    output = value_out[i];
    res    = eval_candidate (btor, exp, inputs, output, value_in_map);
    btor_bv_add_to_tuple (mm, sig, res, i);
    btor_bv_free (mm, res);
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

  if (sig) *sig = btor_bv_new_tuple (mm, nvalues);

  if (matchbv) bv = btor_bv_new (mm, nvalues);

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

    if (btor_bv_compare (res, output) == 0)
    {
      nmatches++;
      if (matchbv) btor_bv_set_bit (bv, i, 1);
    }
    else if (is_equal)
      is_equal = false;

    if (sig) btor_bv_add_to_tuple (mm, *sig, res, i);
    btor_bv_free (mm, res);
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
                      Op *op)
{
  bool found_candidate = false;
  int32_t id;
  BtorBitVectorTuple *sig = 0, *sig_exp;
  BtorBitVector *matchbv  = 0;
  BtorMemMgr *mm;

  id = btor_node_get_id (exp);
  mm = btor->mm;

  if (btor_node_is_bv_const (exp) || btor_hashint_table_contains (cache, id))
  {
    btor_node_release (btor, exp);
    return false;
  }

  if (nexps == 0 || btor_node_real_addr (exp)->sort_id == target_sort)
  {
    /* check signature for candidate expression (in/out values) */
    sig_exp = create_signature_exp (
        btor, exp, value_in, value_out, nvalues, value_in_map);

    if (btor_hashptr_table_get (sigs_exp, sig_exp))
    {
      btor_bv_free_tuple (mm, sig_exp);
      btor_node_release (btor, exp);
      return false;
    }
    btor_hashptr_table_add (sigs_exp, sig_exp);

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
                                            0,
                                            &matchbv);
  }

  if (sig && btor_hashptr_table_get (sigs, sig))
  {
    assert (!found_candidate);
    btor_bv_free_tuple (mm, sig);
    btor_bv_free (mm, matchbv);
    btor_node_release (btor, exp);
    return false;
  }

  if (matchbv) btor_bv_free (mm, matchbv);

  if (sig) btor_hashptr_table_add (sigs, sig);
  btor_hashint_table_add (cache, id);
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
  delta = btor_util_time_stamp () - start;
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
                                            &ops[i]);                     \
    num_checks++;                                                         \
    if (num_checks % 10000 == 0)                                          \
      report_stats (btor, start, cur_level, num_checks, &candidates);     \
    if (num_checks % 1000 == 0 && btor_terminate (btor))                  \
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
  BtorPtrHashTable *sigs, *sigs_exp;
  BtorHashTableData *d;
  BtorMemMgr *mm;
  BtorPartitionGenerator pg;
  BtorCartProdIterator cpit;
  BtorPtrHashTableIterator it;
  BtorSortId bool_sort, target_sort;
  BtorBitVectorPtrStack sig_constraints;
  BtorBitVector *bv, **tmp_value_out;
  BtorIntHashTable *value_cache, *cone_hash;
  BtorIntHashTablePtrStack value_caches;

  start     = btor_util_time_stamp ();
  mm        = btor->mm;
  bool_sort = btor_sort_bool (btor);
  cache     = btor_hashint_table_new (mm);
  cone_hash = btor_hashint_table_new (mm);
  sigs      = btor_hashptr_table_new (
      mm, (BtorHashPtr) btor_bv_hash_tuple, (BtorCmpPtr) btor_bv_compare_tuple);
  sigs_exp = btor_hashptr_table_new (
      mm, (BtorHashPtr) btor_bv_hash_tuple, (BtorCmpPtr) btor_bv_compare_tuple);

  BTOR_INIT_STACK (mm, sig_constraints);
  BTOR_INIT_STACK (mm, trav_exps);
  BTOR_INIT_STACK (mm, trav_cone);
  BTOR_INIT_STACK (mm, value_caches);

  memset (&candidates, 0, sizeof (Candidates));
  BTOR_INIT_STACK (mm, candidates.exps);
  BTOR_PUSH_STACK (candidates.exps, 0);
  BTOR_INIT_STACK (mm, candidates.nexps_level);
  BTOR_PUSH_STACK (candidates.nexps_level, 0);

  target_sort = btor_sort_bv (btor, value_out[0]->width);

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
      value_cache = btor_hashint_map_new (mm);
      bv          = eval_exps (btor,
                      trav_exps.start,
                      BTOR_COUNT_STACK (trav_exps),
                      value_cache,
                      0,
                      0,
                      value_in[i],
                      value_out[i],
                      value_in_map);
      assert (btor_opt_get (btor, BTOR_OPT_QUANT_SYNTH) != BTOR_QUANT_SYNTH_ELMR
              || btor_bv_is_ones (bv));
      BTOR_PUSH_STACK (sig_constraints, bv);
      BTOR_PUSH_STACK (value_caches, value_cache);
    }
    value_out = sig_constraints.start;
    assert (nvalues == BTOR_COUNT_STACK (sig_constraints));
    assert (nvalues == BTOR_COUNT_STACK (value_caches));
  }

  if (prev_synth)
  {
    exp             = btor_node_copy (btor, prev_synth);
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
                                            0);
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
    exp             = btor_node_copy (btor, inputs[i]);
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
    if (btor_bv_compare (tmp_value_out[i - 1], tmp_value_out[i]))
    {
      equal = false;
      break;
    }
  }
  if (equal)
  {
    found_candidate = true;
    exp             = btor_exp_bv_const (btor, tmp_value_out[0]);
    add_exp (btor, 1, &candidates, exp);
    goto DONE;
  }

  /* add constants to level 1 */
  for (i = 0; i < nconsts; i++)
    add_exp (btor, 1, &candidates, btor_node_copy (btor, consts[i]));

#if 0
  /* add the desired outputs as constants to level 1 */
  for (i = 0; i < nvalues; i++)
    {
      exp = btor_exp_bv_const (btor, tmp_value_out[i]);
      add_exp (btor, 1, &candidates, exp);
    }
#endif

  /* level 2+ checks */
  for (cur_level = 2; !max_level || cur_level < max_level; cur_level++)
  {
    /* initialize current level */
    BTOR_PUSH_STACK (candidates.exps, btor_hashint_map_new (mm));
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
          d = btor_hashint_map_get (e0_exps, bool_sort);
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
    result = btor_node_copy (btor, exp);
  else
  {
    equal = true;
    for (i = 1; i < nvalues; i++)
    {
      if (btor_bv_compare (tmp_value_out[i - 1], tmp_value_out[i]))
      {
        equal = false;
        break;
      }
    }
    if (equal)
    {
      found_candidate = true;
      result          = btor_exp_bv_const (btor, tmp_value_out[0]);
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
        btor_node_release (btor, BTOR_POP_STACK (*exps));
      BTOR_RELEASE_STACK (*exps);
      BTOR_DELETE (mm, exps);
    }
    btor_hashint_map_delete (e0_exps);
  }
  BTOR_RELEASE_STACK (candidates.exps);
  BTOR_RELEASE_STACK (candidates.nexps_level);

  while (!BTOR_EMPTY_STACK (value_caches))
  {
    value_cache = BTOR_POP_STACK (value_caches);
    for (j = 0; j < value_cache->size; j++)
    {
      if (!value_cache->data[j].as_ptr) continue;
      btor_bv_free (mm, value_cache->data[j].as_ptr);
    }
    btor_hashint_map_delete (value_cache);
  }
  BTOR_RELEASE_STACK (value_caches);

  while (!BTOR_EMPTY_STACK (sig_constraints))
    btor_bv_free (mm, BTOR_POP_STACK (sig_constraints));
  BTOR_RELEASE_STACK (sig_constraints);

  btor_iter_hashptr_init (&it, sigs);
  btor_iter_hashptr_queue (&it, sigs_exp);
  while (btor_iter_hashptr_has_next (&it))
    btor_bv_free_tuple (mm, btor_iter_hashptr_next (&it));

  btor_hashptr_table_delete (sigs);
  btor_hashptr_table_delete (sigs_exp);
  btor_hashint_table_delete (cache);
  btor_hashint_table_delete (cone_hash);
  BTOR_RELEASE_STACK (trav_exps);
  BTOR_RELEASE_STACK (trav_cone);

  assert (!result || btor_node_real_addr (result)->sort_id == target_sort);
  btor_sort_release (btor, bool_sort);
  btor_sort_release (btor, target_sort);
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

  INIT_OP (1, false, btor_exp_bv_not);
  //  INIT_OP (1, false, btor_neg_exp);
  //  INIT_OP (1, false, btor_redor_exp);
  //  INIT_OP (1, false, btor_redxor_exp);
  //  INIT_OP (1, false, btor_redand_exp);
  //  INIT_OP (1, false, btor_inc_exp);
  //  INIT_OP (1, false, btor_dec_exp);

  /* boolean ops */
  INIT_OP (2, false, btor_exp_bv_ult);
  INIT_OP (2, false, btor_exp_bv_slt);
  INIT_OP (2, true, btor_exp_eq);

  /* bv ops */
  if (btor->ops[BTOR_BV_AND_NODE].cur > 0) INIT_OP (2, true, btor_exp_bv_and);
  if (btor->ops[BTOR_BV_ADD_NODE].cur > 0)
  {
    INIT_OP (2, true, btor_exp_bv_add);
    INIT_OP (2, false, btor_exp_bv_sub);
  }
  if (btor->ops[BTOR_BV_MUL_NODE].cur > 0) INIT_OP (2, true, btor_exp_bv_mul);
  if (btor->ops[BTOR_BV_UDIV_NODE].cur > 0)
  {
    INIT_OP (2, false, btor_exp_bv_udiv);
    INIT_OP (2, false, btor_exp_bv_sdiv);
  }
  if (btor->ops[BTOR_BV_UREM_NODE].cur > 0)
  {
    INIT_OP (2, false, btor_exp_bv_urem);
    INIT_OP (2, false, btor_exp_bv_srem);
    INIT_OP (2, false, btor_exp_bv_smod);
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
  INIT_OP (2, false, btor_exp_bv_slt);
  INIT_OP (2, false, btor_ugt_exp);
  INIT_OP (2, false, btor_sgt_exp);
  INIT_OP (2, false, btor_ugte_exp);
  INIT_OP (2, false, btor_sgte_exp);
  INIT_OP (2, false, btor_exp_bv_sub);
  INIT_OP (2, false, btor_usubo_exp);
  INIT_OP (2, false, btor_ssubo_exp);
  INIT_OP (2, false, btor_exp_bv_udiv);
  INIT_OP (2, false, btor_exp_bv_sdiv);
  INIT_OP (2, false, btor_sdivo_exp);
  INIT_OP (2, false, btor_exp_bv_urem);
  INIT_OP (2, false, btor_exp_bv_srem);
  INIT_OP (2, false, btor_exp_bv_smod);
  INIT_OP (2, false, btor_concat_exp);
#endif
  INIT_OP (3, false, btor_exp_cond);
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
