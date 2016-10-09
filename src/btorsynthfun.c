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

BTOR_DECLARE_STACK (BtorBitVectorTuplePtr, BtorBitVectorTuple *);

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
};

typedef struct Op Op;

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
eval_exp (Btor *btor,
          BtorNode *root,
          BtorNode *candidate,
          BtorBitVectorTuple *value_in,
          BtorBitVector *value_out,
          BtorIntHashTable *value_in_map)
{
  assert (btor);
  assert (root);

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
  BTOR_PUSH_STACK (mm, visit, root);
  while (!BTOR_EMPTY_STACK (visit))
  {
    cur      = BTOR_POP_STACK (visit);
    real_cur = BTOR_REAL_ADDR_NODE (cur);

    d = btor_get_int_hash_map (cache, real_cur->id);
    if (!d)
    {
      if (candidate && btor_is_param_node (real_cur)
          && btor_get_int_hash_map (value_in_map, real_cur->id)->as_int == -1)
      {
        assert (real_cur->sort_id == BTOR_REAL_ADDR_NODE (candidate)->sort_id);
        BTOR_PUSH_STACK (mm, visit, BTOR_COND_INVERT_NODE (cur, candidate));
        continue;
      }

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
        case BTOR_BV_VAR_NODE:
        case BTOR_APPLY_NODE:
          assert (btor_get_int_hash_map (value_in_map, real_cur->id));
          pos = btor_get_int_hash_map (value_in_map, real_cur->id)->as_int;
          /* initial signature computation */
          if (pos == -1)
          {
            assert (value_out);
            assert (!candidate);
            result = btor_copy_bv (mm, value_out);
            assert (btor_get_exp_width (btor, real_cur) == value_out->width);
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
mk_fun (Btor *btor, BtorNode *params[], uint32_t nparams, BtorNode *body)
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
    p     = params[i];
    new_p = btor_param_exp (btor, btor_get_exp_width (btor, p), 0);
    BTOR_PUSH_STACK (mm, new_params, new_p);
    btor_map_node (map, p, new_p);
  }
  assert (BTOR_COUNT_STACK (new_params) == nparams);

  new_body = subst_params (btor, body, map);
  result   = btor_fun_exp (btor, new_params.start, nparams, new_body);
  assert (btor_get_fun_arity (btor, result) == nparams);

  while (!BTOR_EMPTY_STACK (new_params))
    btor_release_exp (btor, BTOR_POP_STACK (new_params));
  BTOR_RELEASE_STACK (mm, new_params);
  btor_release_exp (btor, new_body);
  btor_delete_node_map (map);
  //  assert (!BTOR_REAL_ADDR_NODE (result)->parameterized);
  return result;
}

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
    //	      printf ("new min; %u\n", min_rem_bits);
		}

	      if (cur_rem_bits == 0)
		{
    //	      printf ("found full coverage\n");
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
    //	  printf ("more cov match: %u (%u), ", minm->num_matches, minm->level);
    //	  btor_print_bv (minm->matches);
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

static BtorBitVector *
constraints_signature (Btor *btor,
                       BtorNode *candidate,
                       BtorNode *constraints[],
                       uint32_t nconstraints,
                       BtorBitVectorTuple *value_in,
                       BtorBitVector *value_out,
                       BtorIntHashTable *value_in_map)
{
  uint32_t i;
  BtorBitVector *bv, *ebv;
  BtorMemMgr *mm;

  mm = btor->mm;
  bv = btor_new_bv (mm, nconstraints);
  for (i = 0; i < nconstraints; i++)
  {
    ebv = eval_exp (
        btor, constraints[i], candidate, value_in, value_out, value_in_map);
    assert (ebv->width == 1);
    btor_set_bit_bv (bv, i, btor_get_bit_bv (ebv, 0));
    btor_free_bv (mm, ebv);
  }

  return bv;
}

static bool
check_signature (Btor *btor,
                 BtorNode *exp,
                 BtorBitVectorTuple *value_in[],
                 BtorBitVector *value_out[],
                 uint32_t nvalues,
                 BtorIntHashTable *value_in_map,
                 BtorBitVectorTuple **sig,
                 uint32_t *num_matches,
                 BtorBitVector **matchbv,
                 BtorNode *constraints[],
                 uint32_t nconstraints)
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
    //      assert (value_in_map->count == inputs->arity);

    if (constraints)
      res = constraints_signature (
          btor, exp, constraints, nconstraints, inputs, output, value_in_map);
    else
      res = eval_exp (btor, exp, 0, inputs, 0, value_in_map);

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
check_candidate (Btor *btor,
                 uint32_t cur_level,
                 BtorNode *exp,
                 BtorSortId target_sort,
                 BtorBitVectorTuple *value_in[],
                 BtorBitVector *value_out[],
                 uint32_t nvalues,
                 BtorIntHashTable *value_in_map,
                 BtorVoidPtrStack *candidates,
                 BtorIntHashTable *cache,
                 BtorPtrHashTable *sigs,
                 BtorPtrHashTable *matches,
                 BtorNode *constraints[],
                 uint32_t nconstraints)
{
  bool found_candidate;
  int32_t id;
  uint32_t num_matches = 0;
  BtorBitVectorTuple *sig;
  BtorBitVector *matchbv;
  BtorMemMgr *mm;
  Match *m;

  id = BTOR_GET_ID_NODE (exp);
  mm = btor->mm;

  if (btor_is_bv_const_node (exp) || btor_contains_int_hash_table (cache, id)
      || (nconstraints > 0
          && BTOR_REAL_ADDR_NODE (exp)->sort_id != target_sort))
  {
    btor_release_exp (btor, exp);
    return false;
  }

  found_candidate = check_signature (btor,
                                     exp,
                                     value_in,
                                     value_out,
                                     nvalues,
                                     value_in_map,
                                     &sig,
                                     &num_matches,
                                     &matchbv,
                                     constraints,
                                     nconstraints);

  if (btor_get_ptr_hash_table (sigs, sig))
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
  else
    btor_free_bv (mm, matchbv);

  btor_add_ptr_hash_table (sigs, sig);
  btor_add_int_hash_table (cache, id);
  add_exp (btor, cur_level, candidates, exp);
  return found_candidate;
}

static inline void
report_stats (Btor *btor,
              double start,
              uint32_t cur_level,
              uint32_t num_checks,
              BtorPtrHashTable *sigs)
{
  double delta;
  delta = btor_time_stamp () - start;
  BTOR_MSG (btor->msg,
            1,
            "level: %u|%u|%u, %.2f/s, %.2fs, %.2f MiB",
            cur_level,
            sigs->count,
            num_checks,
            num_checks / delta,
            delta,
            (float) btor->mm->allocated / 1024 / 1024);
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

static void
add_consts (Btor *btor,
            uint32_t width,
            BtorVoidPtrStack *candidates,
            BtorIntHashTable *cache)
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
            BtorIntHashTable *constraints_input_map,
            uint32_t max_checks,
            uint32_t max_level)
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
  BtorNodePtrStack *exps;
  BtorVoidPtrStack candidates;
  BtorIntHashTable *value_in_map, *cache, *e0_exps, *e1_exps, *e2_exps;
  BtorPtrHashTable *matches, *sigs;
  BtorHashTableData *d;
  BtorMemMgr *mm;
  BtorPartitionGenerator pg;
  BtorCartProdIterator cpit;
  BtorHashTableIterator it;
  BtorSortId bool_sort, target_sort;
  BtorBitVectorPtrStack sig_constraints;
  BtorBitVector *bv, **tmp_value_out;

  mm           = btor->mm;
  bool_sort    = btor_bool_sort (&btor->sorts_unique_table);
  value_in_map = btor_new_int_hash_map (mm);
  cache        = btor_new_int_hash_table (mm);
  matches      = btor_new_ptr_hash_table (
      mm, (BtorHashPtr) hash_match, (BtorCmpPtr) cmp_match);
  sigs = btor_new_ptr_hash_table (
      mm, (BtorHashPtr) btor_hash_bv_tuple, (BtorCmpPtr) btor_compare_bv_tuple);
  start = btor_time_stamp ();
  BTOR_INIT_STACK (sig_constraints);
  BTOR_INIT_STACK (candidates);
  BTOR_PUSH_STACK (mm, candidates, 0);

  /* map inputs to their resp. index in 'inputs' in order to have fast
   * access of assignment tuples (value_in) during expression evaluation */
  for (i = 0; i < ninputs; i++)
  {
    assert (BTOR_IS_REGULAR_NODE (inputs[i]));
    btor_add_int_hash_map (value_in_map, inputs[i]->id)->as_int = i;
  }
  target_sort =
      btor_bitvec_sort (&btor->sorts_unique_table, value_out[0]->width);

  tmp_value_out = value_out;
  if (constraints)
  {
    for (i = 0; i < constraints_input_map->size; i++)
    {
      if (!constraints_input_map->keys[i]) continue;
      btor_add_int_hash_map (value_in_map, constraints_input_map->keys[i])
          ->as_int = constraints_input_map->data[i].as_int;
    }
    for (i = 0; i < nvalues; i++)
    {
      bv = constraints_signature (btor,
                                  0,
                                  constraints,
                                  nconstraints,
                                  value_in[i],
                                  value_out[i],
                                  value_in_map);
      btor_print_bv (bv);
      BTOR_PUSH_STACK (mm, sig_constraints, bv);
    }
    value_out = sig_constraints.start;
    assert (nvalues == BTOR_COUNT_STACK (sig_constraints));
  }

  /* level 1 checks (inputs) */
  for (i = 0; i < ninputs; i++)
  {
    exp             = btor_copy_exp (btor, inputs[i]);
    found_candidate = check_candidate (btor,
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
                                       matches,
                                       constraints,
                                       nconstraints);
    add_consts (btor, btor_get_exp_width (btor, exp), &candidates, cache);
    num_checks++;
    if (num_checks % 10000 == 0)
      report_stats (btor, start, cur_level, num_checks, sigs);
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

  /* add the desired outputs as constants to level 1 */
  for (i = 0; i < nvalues; i++)
  {
    exp = btor_const_exp (btor, tmp_value_out[i]);
    add_exp (btor, 1, &candidates, exp);
  }

  /* level 2+ checks */
  for (cur_level = 2; !max_level || cur_level < max_level; cur_level++)
  {
    /* initialize current level */
    BTOR_PUSH_STACK (mm, candidates, btor_new_int_hash_map (mm));
    assert (cur_level == BTOR_COUNT_STACK (candidates) - 1);
    report_stats (btor, start, cur_level, num_checks, sigs);

    num_added = sigs->count;
    for (i = 0; i < nops; i++)
    {
      if (ops[i].arity == 1)
      {
        /* use all expressions from previous level and apply unary
         * operators */
        e0_exps = BTOR_PEEK_STACK (candidates, cur_level - 1);
        for (j = 0; j < e0_exps->size; j++)
        {
          if (!e0_exps->keys[j]) continue;
          exps = e0_exps->data[j].as_ptr;
          for (k = 0; k < BTOR_COUNT_STACK (*exps); k++)
          {
            exp             = ops[i].un (btor, BTOR_PEEK_STACK (*exps, k));
            found_candidate = check_candidate (btor,
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
                                               matches,
                                               constraints,
                                               nconstraints);
            num_checks++;
            if (num_checks % 10000 == 0)
              report_stats (btor, start, cur_level, num_checks, sigs);
            if (found_candidate || num_checks >= max_checks) goto DONE;
            //		      num_un_exps++;
          }
        }
      }
      else if (ops[i].arity == 2)
      {
        btor_init_part_gen (&pg, cur_level, 2, !ops[i].assoc);
        while (btor_has_next_part_gen (&pg))
        {
          tuple   = btor_next_part_gen (&pg);
          e0_exps = BTOR_PEEK_STACK (candidates, tuple[0]);
          e1_exps = BTOR_PEEK_STACK (candidates, tuple[1]);

          btor_init_cart_prod_iterator (&cpit, e0_exps, e1_exps);
          while (btor_has_next_cart_prod_iterator (&cpit))
          {
            exp_tuple       = btor_next_cart_prod_iterator (&cpit);
            exp             = ops[i].bin (btor, exp_tuple[0], exp_tuple[1]);
            found_candidate = check_candidate (btor,
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
                                               matches,
                                               constraints,
                                               nconstraints);
            num_checks++;
            if (num_checks % 10000 == 0)
              report_stats (btor, start, cur_level, num_checks, sigs);
            if (found_candidate || num_checks >= max_checks) goto DONE;
            //		      num_bin_exps++;
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
              exp = ops[i].ter (
                  btor, BTOR_PEEK_STACK (*exps, j), exp_tuple[0], exp_tuple[1]);
              found_candidate = check_candidate (btor,
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
                                                 matches,
                                                 constraints,
                                                 nconstraints);
              num_checks++;
              if (num_checks % 10000 == 0)
                report_stats (btor, start, cur_level, num_checks, sigs);
              if (found_candidate || num_checks >= max_checks) goto DONE;
              //			  num_ter_exps++;
            }
          }
        }
      }
    }
    /* no more expressions generated */
    if (num_added == sigs->count) break;
  }
DONE:
  report_stats (btor, start, cur_level, num_checks, sigs);
  //  max_chain_length (sigs);

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

  /* cleanup */
  for (i = 1; i < BTOR_COUNT_STACK (candidates); i++)
  {
    e0_exps = BTOR_PEEK_STACK (candidates, i);
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
  BTOR_RELEASE_STACK (mm, candidates);

  while (!BTOR_EMPTY_STACK (sig_constraints))
    btor_free_bv (mm, BTOR_POP_STACK (sig_constraints));
  BTOR_RELEASE_STACK (mm, sig_constraints);

  btor_init_hash_table_iterator (&it, matches);
  while (btor_has_next_hash_table_iterator (&it))
    delete_match (mm, btor_next_hash_table_iterator (&it));

  btor_init_hash_table_iterator (&it, sigs);
  while (btor_has_next_hash_table_iterator (&it))
    btor_free_bv_tuple (mm, btor_next_hash_table_iterator (&it));

  btor_delete_ptr_hash_table (sigs);
  btor_delete_ptr_hash_table (matches);
  btor_delete_int_hash_map (value_in_map);
  btor_delete_int_hash_table (cache);

  assert (!result || BTOR_REAL_ADDR_NODE (result)->sort_id == target_sort);
  btor_release_sort (&btor->sorts_unique_table, bool_sort);
  btor_release_sort (&btor->sorts_unique_table, target_sort);
  return result;
}

#define INIT_OP(ARITY, ASSOC, FPTR) \
  {                                 \
    ops[i].arity = ARITY;           \
    ops[i].assoc = ASSOC;           \
    ops[i].fun   = FPTR;            \
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
btor_synthesize_fun (Btor *btor,
                     const BtorPtrHashTable *model,
                     BtorNode *prev_synth_fun,
                     BtorPtrHashTable *additional_inputs,
                     BtorNode *consts[],
                     uint32_t nconsts,
                     uint32_t max_checks,
                     uint32_t max_level)
{
  bool prev_synth_ok;
  uint32_t i, j, nops, ninputs;
  Op ops[64];
  BtorNodePtrStack params, inputs, results;
  BtorNode *p, *in, *candidate, *result = 0;
  BtorMemMgr *mm;
  BtorBitVector *bv;
  BtorBitVectorTuple *tup, *vin, *tmp;
  BtorBitVectorTuplePtrStack value_in;
  BtorBitVectorPtrStack value_out;
  BtorPtrHashTable *m;
  BtorHashTableIterator it;
  BtorPtrHashBucket *b;
  BtorIntHashTable *value_in_map;
  BtorNodeIterator nit;

  mm   = btor->mm;
  nops = init_ops (btor, ops);
  assert (nops);
  BTOR_INIT_STACK (params);
  BTOR_INIT_STACK (inputs);
  BTOR_INIT_STACK (value_in);
  BTOR_INIT_STACK (value_out);
  BTOR_INIT_STACK (results);

  if (prev_synth_fun)
  {
    value_in_map = btor_new_int_hash_map (mm);
    i            = 0;
    btor_init_param_iterator (&nit, prev_synth_fun);
    while (btor_has_next_param_iterator (&nit))
    {
      p = btor_next_param_iterator (&nit);
      btor_add_int_hash_map (value_in_map, p->id)->as_int = i++;
    }
  }

  /* create parameters */
  tup = model->first->key;
  for (i = 0; i < tup->arity; i++)
  {
    p = btor_param_exp (btor, tup->bv[i]->width, 0);
    BTOR_PUSH_STACK (mm, params, p);
    BTOR_PUSH_STACK (mm, inputs, p);
  }

  /* add additional non-parameter inputs */
  if (additional_inputs)
  {
    btor_init_node_hash_table_iterator (&it, additional_inputs);
    while (btor_has_next_node_hash_table_iterator (&it))
    {
      in = btor_next_node_hash_table_iterator (&it);
      assert (BTOR_REAL_ADDR_NODE (in)->arity == 0);
      assert (btor_is_param_node (in));
      BTOR_PUSH_STACK (mm, inputs, in);
    }
  }

  printf ("---------\n");
  /* create input/output assignment pairs */
  ninputs = BTOR_COUNT_STACK (inputs);
  btor_init_hash_table_iterator (&it, model);
  while (btor_has_next_hash_table_iterator (&it))
  {
    bv = it.bucket->data.as_ptr;
    BTOR_PUSH_STACK (mm, value_out, bv);
    printf ("out: %zu ", btor_bv_to_uint64_bv (bv));
    btor_print_bv (bv);

    tup = btor_next_hash_table_iterator (&it);
    vin = btor_new_bv_tuple (mm, ninputs);
    i   = 0;
    for (; i < tup->arity; i++)
    {
      printf (" in: %zu ", btor_bv_to_uint64_bv (tup->bv[i]));
      btor_print_bv (tup->bv[i]);
      btor_add_to_bv_tuple (mm, vin, tup->bv[i], i);
    }
    for (; i < ninputs; i++)
    {
      assert (additional_inputs);
      in = BTOR_PEEK_STACK (inputs, i);
      b  = btor_get_ptr_hash_table (additional_inputs, in);
      assert (b);
      if (b->data.flag)
      {
        assert (BTOR_IS_REGULAR_NODE (in));
        assert (in->parameterized);
        m   = b->data.as_ptr;
        tmp = m->first->key;
        tmp = btor_new_bv_tuple (mm, tmp->arity);
        assert (tmp->arity <= tup->arity);
        for (j = 0; j < tmp->arity; j++)
          btor_add_to_bv_tuple (mm, tmp, tup->bv[j], j);
        b = btor_get_ptr_hash_table (m, tmp);
        assert (b);
        btor_free_bv_tuple (mm, tmp);
        bv = b->data.as_ptr;
      }
      else
        bv = b->data.as_ptr;
      btor_add_to_bv_tuple (mm, vin, bv, i);
    }
    BTOR_PUSH_STACK (mm, value_in, vin);
  }
  assert (BTOR_COUNT_STACK (value_in) == BTOR_COUNT_STACK (value_out));

  prev_synth_ok = false;
  if (prev_synth_fun)
  {
    prev_synth_ok = check_signature (btor,
                                     btor_binder_get_body (prev_synth_fun),
                                     value_in.start,
                                     value_out.start,
                                     BTOR_COUNT_STACK (value_in),
                                     value_in_map,
                                     0,
                                     0,
                                     0,
                                     0,
                                     0);
    btor_delete_int_hash_map (value_in_map);
  }

  if (prev_synth_ok)
    result = btor_copy_exp (btor, prev_synth_fun);
  else
  {
    candidate = synthesize (btor,
                            inputs.start,
                            ninputs,
                            value_in.start,
                            value_out.start,
                            BTOR_COUNT_STACK (value_in),
                            ops,
                            nops,
                            consts,
                            nconsts,
                            0,
                            0,
                            0,
                            max_checks,
                            max_level);

    /* create function from candidate expression */
    if (candidate)
    {
      result =
          mk_fun (btor, params.start, BTOR_COUNT_STACK (params), candidate);
      btor_release_exp (btor, candidate);
    }
  }

  while (!BTOR_EMPTY_STACK (value_in))
    btor_free_bv_tuple (mm, BTOR_POP_STACK (value_in));
  while (!BTOR_EMPTY_STACK (params))
    btor_release_exp (btor, BTOR_POP_STACK (params));

  BTOR_RELEASE_STACK (mm, results);
  BTOR_RELEASE_STACK (mm, params);
  BTOR_RELEASE_STACK (mm, inputs);
  BTOR_RELEASE_STACK (mm, value_in);
  BTOR_RELEASE_STACK (mm, value_out);
  return result;
}

BtorNode *
btor_synthesize_fun_constraints (Btor *btor,
                                 const BtorPtrHashTable *model,
                                 BtorNode *prev_synth_fun,
                                 BtorNode *var,
                                 BtorNode *constraints[],
                                 uint32_t nconstraints,
                                 BtorNode *cinputs[],
                                 uint32_t ncinputs,
                                 BtorNode *consts[],
                                 uint32_t nconsts,
                                 uint32_t max_checks,
                                 uint32_t max_level)
{
  bool prev_synth_ok;
  uint32_t i, j, nops, ninputs;
  Op ops[64];
  BtorNodePtrStack params, inputs, results;
  BtorNode *p, *in, *candidate, *result = 0;
  BtorMemMgr *mm;
  BtorBitVector *bv;
  BtorBitVectorTuple *tup, *vin, *tmp;
  BtorBitVectorTuplePtrStack value_in;
  BtorBitVectorPtrStack value_out;
  BtorPtrHashTable *m;
  BtorHashTableIterator it;
  BtorPtrHashBucket *b;
  BtorIntHashTable *value_in_map;
  BtorNodeIterator nit;

  mm   = btor->mm;
  nops = init_ops (btor, ops);
  assert (nops);
  BTOR_INIT_STACK (params);
  BTOR_INIT_STACK (inputs);
  BTOR_INIT_STACK (value_in);
  BTOR_INIT_STACK (value_out);
  BTOR_INIT_STACK (results);
  value_in_map = btor_new_int_hash_map (mm);

  btor_add_int_hash_map (value_in_map, var->id)->as_int = -1;

  for (i = 0; i < ncinputs; i++)
    btor_add_int_hash_map (value_in_map, cinputs[i]->id)->as_int = i;

#if 0
  if (prev_synth_fun)
    {
      value_in_map = btor_new_int_hash_map (mm);
      i = 0;
      btor_init_param_iterator (&nit, prev_synth_fun);
      while (btor_has_next_param_iterator (&nit))
	{
	  p = btor_next_param_iterator (&nit);
	  btor_add_int_hash_map (value_in_map, p->id)->as_int = i++;
	}
    }
#endif

  /* create parameters */
  tup = model->first->key;
  for (i = 0; i < tup->arity; i++)
  {
    p = btor_param_exp (btor, tup->bv[i]->width, 0);
    BTOR_PUSH_STACK (mm, params, p);
    BTOR_PUSH_STACK (mm, inputs, p);
  }

  printf ("---------\n");
  for (i = 0; i < nconstraints; i++)
    printf ("constraint[%u]: %s\n", i, node2string (constraints[i]));
  /* create input/output assignment pairs */
  ninputs = BTOR_COUNT_STACK (inputs);
  btor_init_hash_table_iterator (&it, model);
  while (btor_has_next_hash_table_iterator (&it))
  {
    bv = it.bucket->data.as_ptr;
    BTOR_PUSH_STACK (mm, value_out, bv);
    printf ("out: %zu ", btor_bv_to_uint64_bv (bv));
    btor_print_bv (bv);

    tup = btor_next_hash_table_iterator (&it);
    vin = btor_new_bv_tuple (mm, ninputs);
    i   = 0;
    for (; i < tup->arity; i++)
    {
      printf (" in: %zu ", btor_bv_to_uint64_bv (tup->bv[i]));
      btor_print_bv (tup->bv[i]);
      btor_add_to_bv_tuple (mm, vin, tup->bv[i], i);
    }
    BTOR_PUSH_STACK (mm, value_in, vin);
  }

  assert (BTOR_COUNT_STACK (value_in) == BTOR_COUNT_STACK (value_out));

  prev_synth_ok = false;
#if 0
  if (prev_synth_fun)
    {
      prev_synth_ok =
	check_signature (btor, btor_binder_get_body (prev_synth_fun),
		         value_in.start, value_out.start,
			 BTOR_COUNT_STACK (value_in), value_in_map, 0, 0, 0);
      btor_delete_int_hash_map (value_in_map);
    }
#endif

  if (prev_synth_ok)
    result = btor_copy_exp (btor, prev_synth_fun);
  else
  {
    candidate = synthesize (btor,
                            inputs.start,
                            ninputs,
                            value_in.start,
                            value_out.start,
                            BTOR_COUNT_STACK (value_in),
                            ops,
                            nops,
                            consts,
                            nconsts,
                            constraints,
                            nconstraints,
                            value_in_map,
                            max_checks,
                            max_level);

    /* create function from candidate expression */
    if (candidate)
    {
      result =
          mk_fun (btor, params.start, BTOR_COUNT_STACK (params), candidate);
      btor_release_exp (btor, candidate);
    }
  }

  while (!BTOR_EMPTY_STACK (value_in))
    btor_free_bv_tuple (mm, BTOR_POP_STACK (value_in));
  while (!BTOR_EMPTY_STACK (params))
    btor_release_exp (btor, BTOR_POP_STACK (params));

  btor_delete_int_hash_map (value_in_map);
  BTOR_RELEASE_STACK (mm, results);
  BTOR_RELEASE_STACK (mm, params);
  BTOR_RELEASE_STACK (mm, inputs);
  BTOR_RELEASE_STACK (mm, value_in);
  BTOR_RELEASE_STACK (mm, value_out);
  return result;
}
