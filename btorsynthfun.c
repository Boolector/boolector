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
#include "btorbitvec.h"
#include "btorcore.h"
#include "btormodel.h"
#include "utils/btorhashint.h"
#include "utils/btoriter.h"
#include "utils/btorpartgen.h"
#include "utils/btorstack.h"

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
  BtorIntHashTableData *d;

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
eval (Btor *btor, BtorNode *exp, BtorIntHashTable *param_map)
{
  assert (btor);
  assert (exp);

  size_t j;
  int32_t i;
  BtorNode *cur, *real_cur;
  BtorNodePtrStack visit;
  BtorIntHashTable *cache;
  BtorIntHashTableData *d;
  BtorBitVectorPtrStack arg_stack;
  BtorMemMgr *mm;
  BtorBitVector **bv, *result, *inv_result, *a;

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
      for (i = real_cur->arity - 1; i >= 0; i--)
        BTOR_PUSH_STACK (mm, visit, real_cur->e[i]);
    }
    else if (!d->as_ptr)
    {
      arg_stack.top -= real_cur->arity;
      bv = arg_stack.top;

      switch (real_cur->kind)
      {
        case BTOR_BV_CONST_NODE:
          result = btor_copy_bv (mm, btor_const_get_bits (real_cur));
          break;

        case BTOR_PARAM_NODE:
          assert (btor_get_int_hash_map (param_map, real_cur->id));
          a      = btor_get_int_hash_map (param_map, real_cur->id)->as_ptr;
          result = btor_copy_bv (mm, a);
          break;

        case BTOR_SLICE_NODE:
          result = btor_slice_bv (mm,
                                  bv[0],
                                  btor_slice_get_upper (real_cur),
                                  btor_slice_get_lower (real_cur));
          break;

        case BTOR_AND_NODE: result = btor_and_bv (mm, bv[0], bv[1]); break;

        case BTOR_BEQ_NODE: result = btor_eq_bv (mm, bv[0], bv[1]); break;

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
          assert (real_cur->kind == BTOR_BCOND_NODE);
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

/* Check for every input/output pair in the uf model if 'exp' produces
 * the same outputs and generate a signature, which is a tuple of all
 * values produced by 'exp'. */
static bool
check_candidate_exp (Btor *btor,
                     BtorNode *exp,
                     BtorNodePtrStack *params,
                     const BtorPtrHashTable *uf_model,
                     BtorBitVectorTuple **sig)
{
  bool is_equal = true;
  uint32_t i, j;
  BtorHashTableIterator it;
  BtorBitVectorTuple *inputs;
  BtorBitVector *output, *res;
  BtorIntHashTable *param_map;
  BtorMemMgr *mm;
  BtorNode *param;

  mm = btor->mm;

  if (sig) *sig = btor_new_bv_tuple (mm, uf_model->count);

  j = 0;
  btor_init_hash_table_iterator (&it, (BtorPtrHashTable *) uf_model);
  while (btor_has_next_hash_table_iterator (&it))
  {
    output = (BtorBitVector *) it.bucket->data.as_ptr;
    inputs = btor_next_hash_table_iterator (&it);

    assert (BTOR_COUNT_STACK (*params) == inputs->arity);
    param_map = btor_new_int_hash_map (mm);
    for (i = 0; i < inputs->arity; i++)
    {
      param = BTOR_PEEK_STACK (*params, i);
      btor_add_int_hash_map (param_map, param->id)->as_ptr = inputs->bv[i];
    }

    res = eval (btor, exp, param_map);

    if (is_equal)
    {
      if (res->width != output->width)
        is_equal = false;
      else if (btor_compare_bv (res, output) != 0)
        is_equal = false;
    }

    if (sig) btor_add_to_bv_tuple (mm, *sig, res, j++);
    btor_free_bv (mm, res);
    btor_delete_int_hash_map (param_map);
  }
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
  BtorIntHashTableData *d;
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

/* Check if expression 'EXP' was already created, or if it is an expressions
 * that matches the concrete model for the uf.
 * Further, check if its signature was already produced by a previously added
 * expression. If this is the case, do not add 'EXP' to the candidate
 * expressions. */
#define CHECK_CANDIDATE(EXP)                                      \
  {                                                               \
    id = BTOR_GET_ID_NODE (EXP);                                  \
    num_checks++;                                                 \
    if (btor_contains_int_hash_table (cache, id))                 \
    {                                                             \
      btor_release_exp (btor, EXP);                               \
      continue;                                                   \
    }                                                             \
    found_candidate =                                             \
        check_candidate_exp (btor, EXP, &params, uf_model, &sig); \
    if (found_candidate)                                          \
    {                                                             \
      assert (BTOR_REAL_ADDR_NODE (EXP)->sort_id == codomain);    \
      btor_free_bv_tuple (mm, sig);                               \
      goto DONE;                                                  \
    }                                                             \
    if (btor_get_ptr_hash_table (sigs, sig))                      \
    {                                                             \
      btor_free_bv_tuple (mm, sig);                               \
      btor_release_exp (btor, EXP);                               \
      continue;                                                   \
    }                                                             \
    btor_add_ptr_hash_table (sigs, sig);                          \
    btor_add_int_hash_table (cache, id);                          \
    add_exp (btor, cur_size, &candidates, EXP);                   \
  }

struct BinOp
{
  bool assoc;
  BtorBinOp op;
};

typedef struct BinOp BinOp;

BtorNode *
btor_synthesize_fun (Btor *btor,
                     BtorNode *uf,
                     const BtorPtrHashTable *uf_model,
                     BtorNode *candidate)
{
  assert (BTOR_IS_REGULAR_NODE (uf));
  assert (BTOR_IS_UF_NODE (uf));

  bool found_candidate;
  double start, delta;
  int32_t id;
  uint32_t i, j, k, *tuple, cur_size;
  uint32_t num_init_exps, num_un_exps, num_bin_exps, num_ter_exps, num_checks;
  BtorNodePtrStack params, *exps;
  BtorVoidPtrStack candidates;
  BtorTupleSortIterator it;
  BtorHashTableIterator hit;
  BtorNode *p, *candidate_exp, **exp_tuple, *result = 0;
  BtorSortUniqueTable *sorts;
  BtorSortId sort, bool_sort, codomain;
  BtorMemMgr *mm;
  BtorPtrHashTable *sigs;
  BtorIntHashTable *cache, *sorted_exps, *e0_exps, *e1_exps, *e2_exps;
  BtorIntHashTableData *d;
  BtorBitVectorTuple *sig;
  BtorPartitionGenerator pg;
  BtorCartProdIterator cpit;
  BtorUnOp unop;
  BinOp binop;
  BtorTerOp terop;
  BtorUnOp unops[] = {
    btor_not_exp,
    btor_neg_exp,
#if 0
      btor_redor_exp,
      btor_redxor_exp,
      btor_redand_exp,
#endif
    btor_inc_exp,
    btor_dec_exp,
    0
  };
  BinOp binops[] = {
    /* boolean ops */
    {false, btor_ult_exp},
    {true, btor_eq_exp},
    /* bv ops */
    {true, btor_and_exp},
    {true, btor_add_exp},
    {true, btor_mul_exp},
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

  BTOR_INIT_STACK (params);
  BTOR_INIT_STACK (candidates);
  BTOR_PUSH_STACK (mm, candidates, 0);

  sort     = btor_get_domain_fun_sort (sorts, uf->sort_id);
  codomain = btor_get_codomain_fun_sort (sorts, uf->sort_id);

#ifdef PRINT_DBG
  uint32_t num_ops[BTOR_NUM_OPS_NODE];
  memset (num_ops, 0, BTOR_NUM_OPS_NODE * sizeof (uint32_t));
  for (i = 0; i < BTOR_NUM_OPS_NODE; i++) num_ops[i] = btor->ops[i].cur;
#endif

  /* create parameters */
  btor_init_tuple_sort_iterator (&it, sorts, sort);
  while (btor_has_next_tuple_sort_iterator (&it))
  {
    sort = btor_next_tuple_sort_iterator (&it);
    p    = btor_param_exp (btor, btor_get_width_bitvec_sort (sorts, sort), 0);
    BTOR_PUSH_STACK (mm, params, p);
  }

  cur_size = 1;
  if (candidate)
  {
    assert (BTOR_IS_REGULAR_NODE (candidate));
    assert (BTOR_IS_FUN_NODE (candidate));

    BtorNodePtrStack cparams;
    BtorNodeIterator p_it;

    BTOR_INIT_STACK (cparams);
    btor_init_param_iterator (&p_it, candidate);
    while (btor_has_next_param_iterator (&p_it))
    {
      p = btor_next_param_iterator (&p_it);
      BTOR_PUSH_STACK (mm, cparams, p);
    }
    candidate_exp = btor_binder_get_body (candidate);
    id            = BTOR_GET_ID_NODE (candidate_exp);
    num_checks++;
    found_candidate =
        check_candidate_exp (btor, candidate_exp, &cparams, uf_model, 0);
    BTOR_RELEASE_STACK (mm, cparams);
    if (found_candidate)
    {
#ifdef PRINT_DBG
      printf ("NOT CHANGED\n");
#endif
      assert (BTOR_REAL_ADDR_NODE (candidate_exp)->sort_id == codomain);
      //	  btor_free_bv_tuple (mm, sig);
      result = btor_copy_exp (btor, candidate);
      goto CLEANUP;
    }
    //      assert (!btor_get_ptr_hash_table (sigs, sig));
    //      btor_add_ptr_hash_table (sigs, sig);
    //      btor_add_int_hash_table (cache, id);
    //      add_exp (btor, cur_size, &candidates, candidate_exp);
  }

  /* check size one (inital) expressions */
  for (i = 0; i < BTOR_COUNT_STACK (params); i++)
  {
    candidate_exp = btor_copy_exp (btor, BTOR_PEEK_STACK (params, i));
    CHECK_CANDIDATE (candidate_exp);
    num_init_exps++;
  }

  // TODO (ma): max tries?
  start = btor_time_stamp ();
  for (cur_size = 2;; cur_size++)
  {
    /* initialize current level */
    sorted_exps = btor_new_int_hash_map (mm);
    BTOR_PUSH_STACK (mm, candidates, sorted_exps);
    assert (cur_size == BTOR_COUNT_STACK (candidates) - 1);

    delta = btor_time_stamp () - start;
    BTOR_MSG (btor->msg,
              1,
              "size: %u, exps: %u/%u/%u/%u/%u, %.2f/s, %.2fs, %.2f MiB",
              cur_size,
              num_init_exps,
              num_un_exps,
              num_bin_exps,
              num_ter_exps,
              num_checks,
              num_checks / delta,
              delta,
              (float) btor->mm->allocated / 1024 / 1024);
#ifdef PRINT_DBG
    printf ("size: %u, num_exps: %u/%u/%u/%u/%u, %.2f/s, %.2fs, %.2f MiB\n",
            cur_size,
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
    sorted_exps = BTOR_PEEK_STACK (candidates, cur_size - 1);
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
      btor_init_part_gen (&pg, cur_size, 2, !binop.assoc);
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
          CHECK_CANDIDATE (candidate_exp);
          num_bin_exps++;
        }
      }
    }

    if (cur_size < 3) continue;

    for (i = 0, terop = terops[i]; terop; i++, terop = terops[i])
    {
      btor_init_part_gen (&pg, cur_size, 3, true);
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
            CHECK_CANDIDATE (candidate_exp);
            num_ter_exps++;
          }
        }
      }
    }
  }

DONE:
  delta = btor_time_stamp () - start;
  BTOR_MSG (btor->msg,
            1,
            "size: %u, exps: %u/%u/%u/%u/%u, %.2f/s, %.2fs, %.2f MiB",
            cur_size,
            num_init_exps,
            num_un_exps,
            num_bin_exps,
            num_ter_exps,
            num_checks,
            num_checks / delta,
            delta,
            (float) btor->mm->allocated / 1024 / 1024);
  if (found_candidate)
  {
    result = btor_fun_exp (
        btor, BTOR_COUNT_STACK (params), params.start, candidate_exp);
    btor_release_exp (btor, candidate_exp);
  }

CLEANUP:
  /* cleanup */
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
  btor_delete_int_hash_table (cache);

  btor_init_hash_table_iterator (&hit, sigs);
  while (btor_has_next_hash_table_iterator (&hit))
  {
    sig = btor_next_hash_table_iterator (&hit);
    btor_free_bv_tuple (mm, sig);
  }
  btor_delete_ptr_hash_table (sigs);

  if (result)
  {
#ifdef PRINT_DBG
    printf ("FOUND CANDIDATE\n");
//    btor_dump_btor_node (btor, stdout, result);
//    btor_dump_smt2_node (btor, stdout, result, -1);
#endif
    return result;
  }

#ifdef PRINT_DBG
  printf ("NO CANDIDATE\n");
#endif
  // TODO (ma): not reachable yet, do we need some criteria to stop
  //            finding a synthesized function?
  return btor_generate_lambda_model_from_fun_model (btor, uf, uf_model);
}
