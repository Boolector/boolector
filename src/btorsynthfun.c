/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2016 Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btorsynthfun.h"
#include "btorbeta.h"
#include "btorbitvec.h"
#include "btorcore.h"
#include "btormodel.h"
#include "utils/btorhashint.h"
#include "utils/btoriter.h"
#include "utils/btorpartgen.h"
#include "utils/btorstack.h"
#include "utils/btorutil.h"

// TODO (ma): for debugging only
#include "dumper/btordumpbtor.h"
#include "dumper/btordumpsmt.h"

//#define PRINT_DBG

typedef BtorNode *(*BtorUnOp) (Btor *, BtorNode *);
typedef BtorNode *(*BtorBinOp) (Btor *, BtorNode *, BtorNode *);
typedef BtorNode *(*BtorTerOp) (Btor *, BtorNode *, BtorNode *, BtorNode *);

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

static BtorBitVector *
eval (Btor *btor,
      BtorNode *exp,
      BtorIntHashTable *param_map,
      BtorBitVectorTuple *param_values,
      BtorPtrHashTable *additional_inputs)
{
  assert (btor);
  assert (exp);

  size_t j;
  int32_t i, pos;
  BtorNode *cur, *real_cur, *arg;
  BtorNodePtrStack visit;
  BtorIntHashTable *cache;
  BtorHashTableData *d;
  BtorPtrHashBucket *b;
  BtorPtrHashTable *model;
  BtorBitVectorTuple *t;
  BtorBitVectorPtrStack arg_stack;
  BtorMemMgr *mm;
  BtorBitVector **bv, *result, *inv_result, *a;
  BtorArgsIterator it;

  mm    = btor->mm;
  cache = btor_new_int_hash_map (mm);

  BTOR_INIT_STACK (arg_stack);
  BTOR_INIT_STACK (visit);
  BTOR_PUSH_STACK (mm, visit, exp);
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

      if (!btor_is_apply_node (real_cur))
      {
        arg_stack.top -= real_cur->arity;
        bv = arg_stack.top;
      }

      switch (real_cur->kind)
      {
        case BTOR_BV_CONST_NODE:
          result = btor_copy_bv (mm, btor_const_get_bits (real_cur));
          break;

        case BTOR_PARAM_NODE:
          assert (btor_get_int_hash_map (param_map, real_cur->id));
          pos = btor_get_int_hash_map (param_map, real_cur->id)->as_int;
          assert (pos >= 0);
          assert (pos < (int32_t) param_values->arity);
          result = btor_copy_bv (mm, param_values->bv[pos]);
          break;

        case BTOR_BV_VAR_NODE:
          assert (additional_inputs);
          b = btor_get_ptr_hash_table (additional_inputs, real_cur);
          assert (b);
          result = btor_copy_bv (mm, b->data.as_ptr);
          break;

        case BTOR_APPLY_NODE:
          assert (additional_inputs);
          b = btor_get_ptr_hash_table (additional_inputs, real_cur->e[0]);
          assert (b);
          model = b->data.as_ptr;
          t = btor_new_bv_tuple (mm, btor_get_fun_arity (btor, real_cur->e[0]));
          i = 0;
          btor_init_args_iterator (&it, real_cur->e[1]);
          while (btor_has_next_args_iterator (&it))
          {
            arg = btor_next_args_iterator (&it);
            assert (BTOR_IS_REGULAR_NODE (arg));
            assert (btor_is_param_node (arg));
            assert (btor_get_int_hash_map (param_map, arg->id));
            pos = btor_get_int_hash_map (param_map, arg->id)->as_int;
            assert (pos >= 0);
            assert (pos < (int32_t) param_values->arity);
            btor_add_to_bv_tuple (mm, t, param_values->bv[pos], i++);
          }
          b = btor_get_ptr_hash_table (model, t);
          if (b)
            result = btor_copy_bv (mm, b->data.as_ptr);
          else
            result = btor_new_bv (mm, btor_get_exp_width (btor, real_cur));
          btor_free_bv_tuple (mm, t);
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

        default:
          assert (real_cur->kind == BTOR_COND_NODE);
          if (btor_is_true_bv (bv[0]))
            result = btor_copy_bv (mm, bv[1]);
          else
            result = btor_copy_bv (mm, bv[2]);
      }

      if (!btor_is_apply_node (real_cur))
      {
        for (i = 0; i < real_cur->arity; i++) btor_free_bv (mm, bv[i]);
      }

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

/* Check for every input/output pair in the uf model if 'exp' produces
 * the same outputs and generate a signature, which is a tuple of all
 * values produced by 'exp'. */
static bool
check_candidate_exp (Btor *btor,
                     BtorNode *exp,
                     BtorIntHashTable *param_map,
                     const BtorPtrHashTable *uf_model,
                     BtorPtrHashTable *additional_inputs,
                     BtorBitVectorTuple **sig,
                     uint32_t *num_matches,
                     BtorBitVector **matchbv)
{
  bool is_equal = true;
  uint32_t i = 0, k = 0, j = 0;
  BtorHashTableIterator it;
  BtorBitVectorTuple *inputs;
  BtorBitVector *output, *res, *bv;
  BtorMemMgr *mm;

  mm = btor->mm;

  if (sig) *sig = btor_new_bv_tuple (mm, uf_model->count);

  if (matchbv) bv = btor_new_bv (mm, uf_model->count);

  btor_init_hash_table_iterator (&it, (BtorPtrHashTable *) uf_model);
  while (btor_has_next_hash_table_iterator (&it))
  {
    output = (BtorBitVector *) it.bucket->data.as_ptr;
    inputs = btor_next_hash_table_iterator (&it);
    assert (param_map->count == inputs->arity);
    res = eval (btor, exp, param_map, inputs, additional_inputs);

    if (btor_compare_bv (res, output) == 0)
    {
      k++;
      if (matchbv) btor_set_bit_bv (bv, j, 1);
    }
    else if (is_equal)
      is_equal = false;

    if (sig) btor_add_to_bv_tuple (mm, *sig, res, i++);
    btor_free_bv (mm, res);
    j++;
  }
  if (num_matches) *num_matches = k;
  if (matchbv) *matchbv = bv;
  return is_equal;
}

/* Add expression 'exp' to expression candidates 'candidates' at level
 * 'exp_size'. */
static void
add_exp (Btor *btor,
         uint32_t exp_size,
         BtorVoidPtrStack *candidates,
         BtorNode *exp)
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

  if (exp_size >= BTOR_COUNT_STACK (*candidates))
  {
    sorted_exps = btor_new_int_hash_map (mm);
    BTOR_PUSH_STACK (mm, *candidates, sorted_exps);
    assert (exp_size == BTOR_COUNT_STACK (*candidates) - 1);
  }
  else
    sorted_exps = BTOR_PEEK_STACK (*candidates, exp_size);

  d = btor_get_int_hash_map (sorted_exps, sort);
  if (d)
    exps = d->as_ptr;
  else
  {
    BTOR_CNEW (mm, exps);
    btor_add_int_hash_map (sorted_exps, sort)->as_ptr = exps;
  }
  BTOR_PUSH_STACK (mm, *exps, exp);
}

static BtorNode *
subst_params (Btor *btor, BtorNode *root, BtorNodeMap *map)
{
  size_t j;
  int32_t i;
  BtorMemMgr *mm;
  BtorNodePtrStack visit, args;
  BtorNode *cur, *real_cur, **e, *result;
  BtorIntHashTable *mark;
  BtorHashTableData *d;

  mm   = btor->mm;
  mark = btor_new_int_hash_map (mm);
  BTOR_INIT_STACK (visit);
  BTOR_INIT_STACK (args);

  BTOR_PUSH_STACK (mm, visit, root);
  while (!BTOR_EMPTY_STACK (visit))
  {
    cur      = BTOR_POP_STACK (visit);
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
        if (btor_is_param_node (real_cur))
        {
          result = btor_mapped_node (map, real_cur);
          assert (result);
          result = btor_copy_exp (btor, result);
        }
        else
          result = btor_copy_exp (btor, real_cur);
      }
      else if (real_cur->arity == 1)
      {
        assert (btor_is_slice_node (real_cur));
        result = btor_slice_exp (btor,
                                 e[0],
                                 btor_slice_get_upper (real_cur),
                                 btor_slice_get_lower (real_cur));
      }
      else
        result = btor_create_exp (btor, real_cur->kind, e, real_cur->arity);

      d->as_ptr = btor_copy_exp (btor, result);

      for (i = 0; i < real_cur->arity; i++) btor_release_exp (btor, e[i]);
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
new_fun (Btor *btor, BtorNodePtrStack *params, BtorNode *body)
{
  uint32_t i, arity;
  BtorNodePtrStack new_params;
  BtorNode *p, *new_p, *new_body, *result;
  BtorMemMgr *mm;
  BtorNodeMap *map;

  mm    = btor->mm;
  arity = BTOR_COUNT_STACK (*params);
  BTOR_INIT_STACK (new_params);
  map = btor_new_node_map (btor);
  for (i = 0; i < arity; i++)
  {
    p     = BTOR_PEEK_STACK (*params, i);
    new_p = btor_param_exp (btor, btor_get_exp_width (btor, p), 0);
    BTOR_PUSH_STACK (mm, new_params, new_p);
    btor_map_node (map, p, new_p);
  }
  assert (BTOR_COUNT_STACK (new_params) == arity);

  new_body = subst_params (btor, body, map);
  result   = btor_fun_exp (btor, new_params.start, arity, new_body);
  assert (btor_get_fun_arity (btor, result) == arity);

  while (!BTOR_EMPTY_STACK (new_params))
    btor_release_exp (btor, BTOR_POP_STACK (new_params));
  BTOR_RELEASE_STACK (mm, new_params);
  btor_release_exp (btor, new_body);
  btor_delete_node_map (map);
  assert (!BTOR_REAL_ADDR_NODE (result)->parameterized);
  return result;
}

/* Check if expression 'EXP' was already created, or if it is an expressions
 * that matches the concrete model for the uf.
 * Further, check if its signature was already produced by a previously added
 * expression. If this is the case, do not add 'EXP' to the candidate
 * expressions. */
#define CHECK_CANDIDATE(EXP)                                         \
  {                                                                  \
    id          = BTOR_GET_ID_NODE (EXP);                            \
    sig_matches = 0;                                                 \
    num_checks++;                                                    \
    cur_num_checks++;                                                \
    if (btor_is_bv_const_node (EXP)                                  \
        || btor_contains_int_hash_table (cache, id))                 \
    {                                                                \
      btor_release_exp (btor, EXP);                                  \
      continue;                                                      \
    }                                                                \
    found_candidate = check_candidate_exp (btor,                     \
                                           EXP,                      \
                                           param_map,                \
                                           uf_model,                 \
                                           additional_inputs,        \
                                           &sig,                     \
                                           &sig_matches,             \
                                           &matchbv);                \
    if (!found_candidate && limit && num_checks > limit)             \
    {                                                                \
      btor_free_bv_tuple (mm, sig);                                  \
      btor_release_exp (btor, EXP);                                  \
      btor_free_bv (mm, matchbv);                                    \
      goto DONE;                                                     \
    }                                                                \
    if (btor_get_ptr_hash_table (sigs, sig))                         \
    {                                                                \
      assert (!found_candidate);                                     \
      btor_free_bv_tuple (mm, sig);                                  \
      btor_release_exp (btor, EXP);                                  \
      btor_free_bv (mm, matchbv);                                    \
      continue;                                                      \
    }                                                                \
    if (sig_matches > 0)                                             \
    {                                                                \
      assert (BTOR_REAL_ADDR_NODE (EXP)->sort_id == candidate_sort); \
      m = new_match (mm, cur_level, sig_matches, matchbv, EXP);      \
      if (!btor_get_ptr_hash_table (all_matches, m))                 \
        btor_add_ptr_hash_table (all_matches, m);                    \
      else                                                           \
        delete_match (mm, m);                                        \
    }                                                                \
    else                                                             \
      btor_free_bv (mm, matchbv);                                    \
    btor_add_ptr_hash_table (sigs, sig);                             \
    btor_add_int_hash_table (cache, id);                             \
    add_exp (btor, cur_level, &candidates, EXP);                     \
    if (found_candidate)                                             \
    {                                                                \
      assert (BTOR_REAL_ADDR_NODE (EXP)->sort_id == candidate_sort); \
      goto DONE;                                                     \
    }                                                                \
  }

struct BinOp
{
  bool assoc;
  BtorBinOp op;
};

typedef struct BinOp BinOp;

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

static int32_t
cmp_sort_match (const void *m0, const void *m1)
{
  const Match *m00 = *(Match **) m0;
  const Match *m11 = *(Match **) m1;

  //  if (m00->num_matches == m11->num_matches)
  //    return btor_compare_bv (m00->matches, m11->matches);
  return m00->num_matches - m11->num_matches;
}

static void
delete_match (BtorMemMgr *mm, Match *m)
{
  btor_free_bv (mm, m->matches);
  btor_release_exp (BTOR_REAL_ADDR_NODE (m->exp)->btor, m->exp);
  BTOR_DELETE (mm, m);
}

BTOR_DECLARE_STACK (MatchPtr, Match *);

// TODO (ma): more performance measurements what costs the most?
bool
btor_synthesize_fun (Btor *btor,
                     BtorNode *uf,
                     const BtorPtrHashTable *uf_model,
                     BtorNode *prev_synth_fun,
                     BtorPtrHashTable *additional_inputs,
                     uint32_t limit,
                     uint32_t max_level,
                     BtorNodePtrStack *matches)
{
  assert (matches);
  assert (BTOR_EMPTY_STACK (*matches));

  bool found_candidate;
  double start, delta;
  int32_t id, i;
  uint32_t j, k, *tuple, cur_level, cur_num_checks = 0, sig_matches;
  uint32_t num_init_exps, num_un_exps, num_bin_exps, num_ter_exps, num_checks;
  BtorNodePtrStack params, *exps;
  BtorVoidPtrStack candidates;
  BtorHashTableIterator hit;
  BtorNode *p, *candidate_exp, **exp_tuple, *result = 0;
  BtorSortUniqueTable *sorts;
  BtorSortId bool_sort, candidate_sort;
  BtorMemMgr *mm;
  BtorPtrHashTable *sigs, *all_matches;
  BtorIntHashTable *cache, *sorted_exps, *e0_exps, *e1_exps, *e2_exps;
  BtorIntHashTable *param_map;
  BtorHashTableData *d;
  BtorBitVector *bv, *matchbv;
  BtorBitVectorTuple *sig;
  BtorPartitionGenerator pg;
  BtorCartProdIterator cpit;
  Match *m;
  BtorUnOp unop;
  BinOp binop;
  BtorTerOp terop;
  BtorUnOp unops[] = {
    btor_not_exp,
#if 0
      btor_neg_exp,
      btor_redor_exp,
      btor_redxor_exp,
      btor_redand_exp,
      btor_inc_exp,
      btor_dec_exp,
#endif
    0
  };
  BinOp binops[] = {
    /* boolean ops */
    {false, btor_ult_exp},
    {true, btor_eq_exp},
    /* bv ops */
    {true, btor_and_exp},
    {true, btor_add_exp},
    {false, btor_sub_exp},
    {true, btor_mul_exp},
    {false, btor_udiv_exp},
    {false, btor_urem_exp},
#if 0
      { true,  btor_ne_exp },
      { true,  btor_xor_exp },
      { true,  btor_xnor_exp },
      { true,  btor_nand_exp },
      { true,  btor_or_exp },
      { true,  btor_nor_exp },
      /* additonal ops */
      { true, btor_uaddo_exp },
      { true, btor_saddo_exp },
      { true, btor_umulo_exp },
      { true, btor_smulo_exp },
      { false, btor_slt_exp },
      { false, btor_ugt_exp },
      { false, btor_sgt_exp },
      { false, btor_ugte_exp },
      { false, btor_sgte_exp },
      { false, btor_sub_exp },
      { false, btor_usubo_exp },
      { false, btor_ssubo_exp },
      { false, btor_udiv_exp },
      { false, btor_sdiv_exp },
      { false, btor_sdivo_exp },
      { false, btor_urem_exp },
      { false, btor_srem_exp },
      { false, btor_smod_exp },
      { false, btor_concat_exp },
#endif
    {false, 0},
  };
  BtorTerOp terops[] = {btor_cond_exp, 0};

  mm              = btor->mm;
  found_candidate = false;
  num_init_exps = num_un_exps = num_bin_exps = num_ter_exps = num_checks = 0;
  sorts     = &btor->sorts_unique_table;
  bool_sort = btor_bool_sort (sorts);
  cache     = btor_new_int_hash_table (mm);
  sigs      = btor_new_ptr_hash_table (
      mm, (BtorHashPtr) btor_hash_bv_tuple, (BtorCmpPtr) btor_compare_bv_tuple);
  param_map   = btor_new_int_hash_map (mm);
  all_matches = btor_new_ptr_hash_table (
      mm, (BtorHashPtr) hash_match, (BtorCmpPtr) cmp_match);

  BTOR_INIT_STACK (params);
  BTOR_INIT_STACK (candidates);
  BTOR_PUSH_STACK (mm, candidates, 0);

#ifdef PRINT_DBG
  uint32_t num_ops[BTOR_NUM_OPS_NODE];
  memset (num_ops, 0, BTOR_NUM_OPS_NODE * sizeof (uint32_t));
  for (i = 0; i < BTOR_NUM_OPS_NODE; i++) num_ops[i] = btor->ops[i].cur;
#endif

  /* create parameters */
  sig            = uf_model->first->key;
  bv             = uf_model->first->data.as_ptr;
  candidate_sort = btor_bitvec_sort (sorts, bv->width);
  for (i = 0; i < (int32_t) sig->arity; i++)
  {
    p = btor_param_exp (btor, sig->bv[i]->width, 0);
    BTOR_PUSH_STACK (mm, params, p);
    btor_add_int_hash_map (param_map, p->id)->as_int = i;
  }

  start     = btor_time_stamp ();
  cur_level = 1;
  BTOR_MSG (btor->msg,
            1,
            "function: %s, arity: %u, model size: %u",
            uf ? btor_get_symbol_exp (btor, uf) : 0,
            BTOR_COUNT_STACK (params),
            uf_model->count);

  /* check previously synthesized functions */
  if (prev_synth_fun)
  {
    num_checks++;
    candidate_exp = btor_apply_and_reduce (
        btor, params.start, BTOR_COUNT_STACK (params), prev_synth_fun);
    found_candidate = check_candidate_exp (
        btor, candidate_exp, param_map, uf_model, additional_inputs, 0, 0, 0);
    btor_release_exp (btor, candidate_exp);
    if (found_candidate)
    {
      result = btor_copy_exp (btor, prev_synth_fun);
      goto DONE;
    }
  }

  if (additional_inputs)
  {
    btor_init_node_hash_table_iterator (&hit, additional_inputs);
    while (btor_has_next_node_hash_table_iterator (&hit))
    {
      p = btor_next_node_hash_table_iterator (&hit);
      assert (BTOR_IS_REGULAR_NODE (p));

      if (btor_is_uf_node (p))
      {
        assert (btor_get_fun_arity (btor, p) == BTOR_COUNT_STACK (params));
        candidate_exp = btor_apply_exps (
            btor, params.start, btor_get_fun_arity (btor, p), p);
      }
      else
      {
        assert (btor_is_bv_var_node (p));
        candidate_exp = btor_copy_exp (btor, p);
      }
      //	  printf ("check: %s\n", node2string (candidate_exp));
      CHECK_CANDIDATE (candidate_exp);
      //	  printf ("added: %s\n", node2string (candidate_exp));
      num_init_exps++;
    }
  }

  /* check size one (inital) expressions */
  for (i = 0; i < BTOR_COUNT_STACK (params); i++)
  {
    candidate_exp = btor_copy_exp (btor, BTOR_PEEK_STACK (params, i));
    //      printf ("check: %s\n", node2string (candidate_exp));
    CHECK_CANDIDATE (candidate_exp);
    //      printf ("added: %s\n", node2string (candidate_exp));
    num_init_exps++;
  }

  // TODO (ma): max tries?
  for (cur_level = 2; !max_level || cur_level < max_level; cur_level++)
  {
    cur_num_checks = 0;
    /* initialize current level */
    sorted_exps = btor_new_int_hash_map (mm);
    BTOR_PUSH_STACK (mm, candidates, sorted_exps);
    assert (cur_level == BTOR_COUNT_STACK (candidates) - 1);

    delta = btor_time_stamp () - start;
    BTOR_MSG (btor->msg,
              1,
              "level: %u, exps: %u/%u/%u/%u/%u, %.2f/s, %.2fs, %.2f MiB",
              cur_level,
              num_init_exps,
              num_un_exps,
              num_bin_exps,
              num_ter_exps,
              num_checks,
              num_checks / delta,
              delta,
              (float) btor->mm->allocated / 1024 / 1024);
#ifdef PRINT_DBG
    printf ("level: %u, num_exps: %u/%u/%u/%u/%u, %.2f/s, %.2fs, %.2f MiB\n",
            cur_level,
            num_init_exps,
            num_un_exps,
            num_bin_exps,
            num_ter_exps,
            num_checks,
            num_checks / delta,
            delta,
            (float) btor->mm->allocated / 1024 / 1024);

    for (i = 0; i < BTOR_NUM_OPS_NODE; i++)
      if (btor->ops[i].cur - num_ops[i] > 0)
        printf ("%s: %d\n", g_btor_op2str[i], btor->ops[i].cur - num_ops[i]);
#endif

    /* use all expressions from previous level and apply unary operators */
    sorted_exps = BTOR_PEEK_STACK (candidates, cur_level - 1);
    for (i = 0, unop = unops[i]; unop; i++, unop = unops[i])
    {
      for (j = 0; j < sorted_exps->size; j++)
      {
        if (!sorted_exps->keys[j]) continue;
        exps = sorted_exps->data[j].as_ptr;
        for (k = 0; k < BTOR_COUNT_STACK (*exps); k++)
        {
          p             = BTOR_PEEK_STACK (*exps, k);
          candidate_exp = unop (btor, p);
          CHECK_CANDIDATE (candidate_exp);
          num_un_exps++;
        }
      }
    }

    for (i = 0, binop = binops[i]; binop.op; i++, binop = binops[i])
    {
      btor_init_part_gen (&pg, cur_level, 2, !binop.assoc);
      while (btor_has_next_part_gen (&pg))
      {
        tuple   = btor_next_part_gen (&pg);
        e0_exps = BTOR_PEEK_STACK (candidates, tuple[0]);
        e1_exps = BTOR_PEEK_STACK (candidates, tuple[1]);

        btor_init_cart_prod_iterator (&cpit, e0_exps, e1_exps);
        while (btor_has_next_cart_prod_iterator (&cpit))
        {
          exp_tuple     = btor_next_cart_prod_iterator (&cpit);
          candidate_exp = binop.op (btor, exp_tuple[0], exp_tuple[1]);
          //		  printf ("check: %s(%d, %d)\n",
          //			  binop.name,
          //			  BTOR_GET_ID_NODE (exp_tuple[0]),
          //			  BTOR_GET_ID_NODE (exp_tuple[1]));
          CHECK_CANDIDATE (candidate_exp);
          //		  printf ("added: %s\n", node2string (candidate_exp));
          num_bin_exps++;
        }
      }
    }

    if (cur_level < 3) continue;

    for (i = 0, terop = terops[i]; terop; i++, terop = terops[i])
    {
      btor_init_part_gen (&pg, cur_level, 3, true);
      while (btor_has_next_part_gen (&pg))
      {
        tuple   = btor_next_part_gen (&pg);
        e0_exps = BTOR_PEEK_STACK (candidates, tuple[0]);
        e1_exps = BTOR_PEEK_STACK (candidates, tuple[1]);
        e2_exps = BTOR_PEEK_STACK (candidates, tuple[2]);

#if 0
	      // TODO (ma): this speeds up AR-fixpoint by ~3 seconds each, but
	      //            is not the original sygus algorithm
	      uint32_t cnt;
	      cnt = tuple[0];
	      while (cnt >= 1)
		{
		  e0_exps = BTOR_PEEK_STACK (candidates, cnt);
		  d = btor_get_int_hash_map (e0_exps, bool_sort);
		  cnt--;
		  if (d)
		    break;
		}
#endif

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
            p             = BTOR_PEEK_STACK (*exps, j);
            candidate_exp = terop (btor, p, exp_tuple[0], exp_tuple[1]);
            //		      printf ("check: cond(%d, %d, %d)\n",
            //			      BTOR_GET_ID_NODE (p),
            //			      BTOR_GET_ID_NODE (exp_tuple[0]),
            //			      BTOR_GET_ID_NODE (exp_tuple[1]));
            CHECK_CANDIDATE (candidate_exp);
            //		      printf ("added: %s\n", node2string
            //(candidate_exp));
            num_ter_exps++;
          }
        }
      }
    }

    if (cur_num_checks == 0) break;
  }

DONE:
  delta = btor_time_stamp () - start;
  BTOR_MSG (btor->msg,
            1,
            "level: %u, exps: %u/%u/%u/%u/%u, %.2f/s, %.2fs, %.2f MiB",
            cur_level,
            num_init_exps,
            num_un_exps,
            num_bin_exps,
            num_ter_exps,
            num_checks,
            num_checks / delta,
            delta,
            (float) btor->mm->allocated / 1024 / 1024);

  /* result may already be set if prev_synth_fun is still a candidate */
  if (!result && found_candidate)
    result = btor_fun_exp (
        btor, params.start, BTOR_COUNT_STACK (params), candidate_exp);

  if (result)
  {
    BTOR_PUSH_STACK (mm, *matches, result);
    //    return result;
  }
  else
  {
    printf ("---\n");
    MatchPtrStack stack;
    BTOR_INIT_STACK (stack);
    btor_init_hash_table_iterator (&hit, all_matches);
    while (btor_has_next_hash_table_iterator (&hit))
    {
      m = btor_next_hash_table_iterator (&hit);
      BTOR_PUSH_STACK (mm, stack, m);
    }

    qsort (stack.start,
           BTOR_COUNT_STACK (stack),
           sizeof (Match *),
           cmp_sort_match);

    matchbv = 0;
    bv      = btor_new_bv (mm, uf_model->count);
    for (i = BTOR_COUNT_STACK (stack) - 1; i >= 0; i--)
    {
      m = BTOR_PEEK_STACK (stack, i);
      if (matchbv) btor_free_bv (mm, matchbv);
      matchbv = bv;
      bv      = btor_or_bv (mm, matchbv, m->matches);
      /* more coverage of input/output pairs */
      if (btor_compare_bv (bv, matchbv))
      {
        printf ("more cov match: %u (%u), ", m->num_matches, m->level);
        btor_print_bv (m->matches);
        BTOR_PUSH_STACK (mm, *matches, new_fun (btor, &params, m->exp));
      }
      if (btor_is_ones_bv (bv))
      {
        printf ("found full coverage\n");
        found_candidate = true;
        break;
      }
    }
    btor_free_bv (mm, bv);
  }

  /* cleanup */
  btor_init_hash_table_iterator (&hit, all_matches);
  while (btor_has_next_hash_table_iterator (&hit))
  {
    m = btor_next_hash_table_iterator (&hit);
    delete_match (mm, m);
  }
  btor_delete_ptr_hash_table (all_matches);

  for (i = 1; i < BTOR_COUNT_STACK (candidates); i++)
  {
    sorted_exps = BTOR_PEEK_STACK (candidates, i);
    for (j = 0; j < sorted_exps->size; j++)
    {
      if (!sorted_exps->data[j].as_ptr) continue;
      exps = sorted_exps->data[j].as_ptr;
      while (!BTOR_EMPTY_STACK (*exps))
        btor_release_exp (btor, BTOR_POP_STACK (*exps));
      BTOR_RELEASE_STACK (mm, *exps);
      BTOR_DELETE (mm, exps);
    }
    btor_delete_int_hash_map (sorted_exps);
  }
  BTOR_RELEASE_STACK (mm, candidates);

  while (!BTOR_EMPTY_STACK (params))
    btor_release_exp (btor, BTOR_POP_STACK (params));
  BTOR_RELEASE_STACK (mm, params);

  btor_release_sort (sorts, bool_sort);
  btor_release_sort (sorts, candidate_sort);
  btor_delete_int_hash_table (cache);
  btor_delete_int_hash_map (param_map);

  btor_init_hash_table_iterator (&hit, sigs);
  while (btor_has_next_hash_table_iterator (&hit))
  {
    sig = btor_next_hash_table_iterator (&hit);
    btor_free_bv_tuple (mm, sig);
  }
  btor_delete_ptr_hash_table (sigs);

  return found_candidate;
}
