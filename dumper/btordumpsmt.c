/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2013 Armin Biere.
 *  Copyright (C) 2012-2013 Aina Niemetz, Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btordumpsmt.h"
#include "btorconst.h"
#include "btorcore.h"
#include "btorexit.h"
#include "btorhash.h"
#include "btoriter.h"

#include <ctype.h>
#include <limits.h>

struct BtorSMTDumpContext
{
  Btor *btor;
  BtorPtrHashTable *dump;
  BtorPtrHashTable *mark;
  BtorPtrHashTable *idtab;
  BtorNodePtrStack roots;
  FILE *file;
  int maxid;
  int pprint;
};

typedef struct BtorSMTDumpContext BtorSMTDumpContext;

static BtorSMTDumpContext *
new_smt_dump_context (Btor *btor, FILE *file)
{
  BtorSMTDumpContext *sdc;
  BTOR_CNEW (btor->mm, sdc);

  sdc->btor   = btor;
  sdc->dump   = btor_new_ptr_hash_table (btor->mm,
                                       (BtorHashPtr) btor_hash_exp_by_id,
                                       (BtorCmpPtr) btor_compare_exp_by_id);
  sdc->mark   = btor_new_ptr_hash_table (btor->mm,
                                       (BtorHashPtr) btor_hash_exp_by_id,
                                       (BtorCmpPtr) btor_compare_exp_by_id);
  sdc->idtab  = btor_new_ptr_hash_table (btor->mm,
                                        (BtorHashPtr) btor_hash_exp_by_id,
                                        (BtorCmpPtr) btor_compare_exp_by_id);
  sdc->file   = file;
  sdc->maxid  = 1;
  sdc->pprint = btor->pprint;

  BTOR_INIT_STACK (sdc->roots);
  return sdc;
}

static void
delete_smt_dump_context (BtorSMTDumpContext *sdc)
{
  btor_delete_ptr_hash_table (sdc->dump);
  btor_delete_ptr_hash_table (sdc->mark);
  btor_delete_ptr_hash_table (sdc->idtab);

  while (!BTOR_EMPTY_STACK (sdc->roots))
    btor_release_exp (sdc->btor, BTOR_POP_STACK (sdc->roots));
  BTOR_RELEASE_STACK (sdc->btor->mm, sdc->roots);

  BTOR_DELETE (sdc->btor->mm, sdc);
}

static void
add_root_to_smt_dump_context (BtorSMTDumpContext *sdc, BtorNode *root)
{
  BTOR_PUSH_STACK (sdc->btor->mm, sdc->roots, btor_copy_exp (sdc->btor, root));
}

static int
btor_cmp_node_id (const void *p, const void *q)
{
  BtorNode *a = *(BtorNode **) p;
  BtorNode *b = *(BtorNode **) q;
  return a->id - b->id;
}

static int
smt_id (BtorSMTDumpContext *sdc, BtorNode *exp)
{
  assert (sdc);
  assert (exp);
  assert (BTOR_IS_REGULAR_NODE (exp));

  BtorPtrHashBucket *b;

  if (sdc->pprint)
  {
    b = btor_find_in_ptr_hash_table (sdc->idtab, exp);

    if (!b)
    {
      b             = btor_insert_in_ptr_hash_table (sdc->idtab, exp);
      b->data.asInt = sdc->maxid++;
    }
    return b->data.asInt;
  }
  return exp->id;
}

static void
btor_dump_smt_id (BtorSMTDumpContext *sdc, BtorNode *exp)
{
  assert (sdc);
  assert (exp);

  const char *type, *sym;
  BtorNode *u;

  u = BTOR_REAL_ADDR_NODE (exp);

  if (u != exp) fputs ("(bvnot ", sdc->file);

  if (BTOR_IS_BV_VAR_NODE (u))
  {
    sym = u->symbol;
    if (!isdigit (sym[0]))
    {
      fputs (sym, sdc->file);
      goto CLOSE;
    }
    type = "v";
  }
  else if (BTOR_IS_PARAM_NODE (u))
  {
    sym = u->symbol;
    if (!isdigit (sym[0]))
    {
      fputs (sym, sdc->file);
      goto CLOSE;
    }
    type = "p";
  }
  else if (BTOR_IS_ARRAY_VAR_NODE (u))
    type = "a";
  else if (BTOR_IS_LAMBDA_NODE (u))
    type = "f";
  else
    type = "$e";

  fprintf (sdc->file, "%s%d", type, smt_id (sdc, u));

CLOSE:
  if (u != exp) fputc (')', sdc->file);
}

static void
btor_dump_bit_smt (BtorSMTDumpContext *sdc, int bit)
{
  assert (bit == 0 || bit == 1);
  fprintf (sdc->file, "#b%d", bit);
}

static void
dump_sort_smt2 (BtorSMTDumpContext *sdc, BtorNode *exp)
{
  assert (sdc);
  assert (exp);

  exp = BTOR_REAL_ADDR_NODE (exp);

  if (BTOR_IS_ARRAY_VAR_NODE (exp))
    fprintf (sdc->file,
             "(Array (_ BitVec %d) (_ BitVec %d))",
             BTOR_ARRAY_INDEX_LEN (exp),
             exp->len);
  //  else if (e->len == 1)
  //    fprintf (file, "Bool");
  else if (exp)
    fprintf (sdc->file, "(_ BitVec %d)", exp->len);
}

static void
dump_declare_fun_smt2 (BtorSMTDumpContext *sdc, BtorNode *exp)
{
  fputs ("(declare-fun ", sdc->file);
  btor_dump_smt_id (sdc, exp);
  fputs (" () ", sdc->file);
  dump_sort_smt2 (sdc, exp);
  fputs (")\n", sdc->file);
}

static void
dump_exp_smt2 (BtorSMTDumpContext *sdc, BtorNode *exp)
{
  assert (sdc);
  assert (exp);
  assert (!btor_find_in_ptr_hash_table (sdc->mark, exp));

  int pad, i;
  char *val;
  const char *op;
  BtorNode *arg;
  BtorMemMgr *mm;
  BtorArgsIterator it;

  mm = sdc->btor->mm;

  switch (exp->kind)
  {
    case BTOR_BV_CONST_NODE:
      val = btor_const_to_decimal (mm, exp->bits);
      fprintf (sdc->file, "(_ bv%s %d)", val, exp->len);
      btor_freestr (mm, val);
      break;

    case BTOR_SLICE_NODE:
      fprintf (sdc->file, "((_ extract %d %d) ", exp->upper, exp->lower);
      btor_dump_smt_id (sdc, exp->e[0]);
      fputc (')', sdc->file);
      break;

    case BTOR_SLL_NODE:
    case BTOR_SRL_NODE:
      fputc ('(', sdc->file);

      if (exp->kind == BTOR_SRL_NODE)
        fputs ("bvlshr", sdc->file);
      else
        fputs ("bvshl", sdc->file);

      fputc (' ', sdc->file);
      btor_dump_smt_id (sdc, exp->e[0]);
      fputc (' ', sdc->file);

      assert (exp->len > 1);
      pad = exp->len - BTOR_REAL_ADDR_NODE (exp->e[1])->len;

      fprintf (sdc->file, " ((_ zero_extend %d) ", pad);

      btor_dump_smt_id (sdc, exp->e[1]);
      fputs ("))", sdc->file);
      break;

    case BTOR_BCOND_NODE:
      fputs ("(ite (= ", sdc->file);
      btor_dump_bit_smt (sdc, 1);
      fputc (' ', sdc->file);
      btor_dump_smt_id (sdc, exp->e[0]);
      fputs (") ", sdc->file);
      btor_dump_smt_id (sdc, exp->e[1]);
      fputc (' ', sdc->file);
      btor_dump_smt_id (sdc, exp->e[2]);
      fputc (')', sdc->file);
      break;

    case BTOR_BEQ_NODE:
    case BTOR_ULT_NODE:
      fputs ("(ite (", sdc->file);
      if (exp->kind == BTOR_ULT_NODE)
        fputs ("bvult", sdc->file);
      else
        fputc ('=', sdc->file);
      fputc (' ', sdc->file);
      btor_dump_smt_id (sdc, exp->e[0]);
      fputc (' ', sdc->file);
      btor_dump_smt_id (sdc, exp->e[1]);
      fputs (") ", sdc->file);
      btor_dump_bit_smt (sdc, 1);
      fputc (' ', sdc->file);
      btor_dump_bit_smt (sdc, 0);
      fputc (')', sdc->file);
      break;

    case BTOR_APPLY_NODE:
      fputc ('(', sdc->file);
      /* array select */
      if (BTOR_IS_ARRAY_VAR_NODE (exp->e[0]))
      {
        fputs ("select ", sdc->file);
        btor_dump_smt_id (sdc, exp->e[0]);
        fputc (' ', sdc->file);
        assert (BTOR_IS_REGULAR_NODE (exp->e[1]));
        assert (((BtorArgsNode *) exp->e[1])->num_args == 1);
        btor_dump_smt_id (sdc, exp->e[1]->e[0]);
      }
      /* function application */
      else
      {
        btor_dump_smt_id (sdc, exp->e[0]);

        init_args_iterator (&it, exp->e[1]);
        while (has_next_args_iterator (&it))
        {
          arg = next_args_iterator (&it);
          fputc (' ', sdc->file);
          btor_dump_smt_id (sdc, arg);
        }
      }
      fputc (')', sdc->file);
      break;

    default:
      fputc ('(', sdc->file);

      switch (exp->kind)
      {
        case BTOR_AND_NODE: op = "bvand"; break;
        case BTOR_ADD_NODE: op = "bvadd"; break;
        case BTOR_MUL_NODE: op = "bvmul"; break;
        case BTOR_UDIV_NODE: op = "bvudiv"; break;
        case BTOR_UREM_NODE: op = "bvurem"; break;
        case BTOR_CONCAT_NODE: op = "concat"; break;
        default: assert (0); op = "unknown";
      }

      fputs (op, sdc->file);

      for (i = 0; i < exp->arity; i++)
      {
        fputc (' ', sdc->file);
        btor_dump_smt_id (sdc, exp->e[i]);
      }

      fputc (')', sdc->file);
  }
  btor_insert_in_ptr_hash_table (sdc->mark, exp);
}

static void
dump_let_smt2 (BtorSMTDumpContext *sdc, BtorNode *exp)
{
  assert (sdc);
  assert (BTOR_IS_REGULAR_NODE (exp));

  fputs ("(let ((", sdc->file);
  btor_dump_smt_id (sdc, exp);
  fputc (' ', sdc->file);

  dump_exp_smt2 (sdc, exp);

  fputs ("))", sdc->file);
}

static void
dump_fun_let_smt2 (BtorSMTDumpContext *sdc, BtorNode *exp)
{
  assert (sdc);
  assert (BTOR_IS_REGULAR_NODE (exp));

  if (btor_find_in_ptr_hash_table (sdc->mark, exp)) return;

  fputs ("(define-fun ", sdc->file);
  btor_dump_smt_id (sdc, exp);
  fputs (" () ", sdc->file);
  dump_sort_smt2 (sdc, exp);
  fputc (' ', sdc->file);
  dump_exp_smt2 (sdc, exp);
  fputs (")\n", sdc->file);
}

static void
dump_fun_smt2 (BtorSMTDumpContext *sdc, BtorNode *fun)
{
  assert (fun);
  assert (BTOR_IS_REGULAR_NODE (fun));
  assert (BTOR_IS_FUN_NODE (fun));
  assert (!fun->parameterized);
  assert (!btor_find_in_ptr_hash_table (sdc->mark, fun));

  int i, lets;
  BtorNode *cur, *param;
  BtorMemMgr *mm = sdc->btor->mm;
  BtorNodePtrStack visit, local, non_local, body;
  BtorNodeIterator it;
  BtorPtrHashTable *mark;

  mark = btor_new_ptr_hash_table (mm,
                                  (BtorHashPtr) btor_hash_exp_by_id,
                                  (BtorCmpPtr) btor_compare_exp_by_id);
  BTOR_INIT_STACK (visit);
  BTOR_INIT_STACK (local);
  BTOR_INIT_STACK (non_local);
  BTOR_INIT_STACK (body);

  /* collect function body */
  BTOR_PUSH_STACK (mm, visit, BTOR_REAL_ADDR_NODE (BTOR_LAMBDA_GET_BODY (fun)));
  while (!BTOR_EMPTY_STACK (visit))
  {
    cur = BTOR_POP_STACK (visit);
    assert (BTOR_IS_REGULAR_NODE (cur));

    if (btor_find_in_ptr_hash_table (mark, cur) || BTOR_IS_FUN_NODE (cur))
      continue;

    /* args and params are handled differently */
    if (!BTOR_IS_ARGS_NODE (cur) && !BTOR_IS_PARAM_NODE (cur))
      BTOR_PUSH_STACK (mm, body, cur);

    btor_insert_in_ptr_hash_table (mark, cur);
    for (i = 0; i < cur->arity; i++)
      BTOR_PUSH_STACK (mm, visit, BTOR_REAL_ADDR_NODE (cur->e[i]));
  }

  if (!BTOR_EMPTY_STACK (body))
    qsort (body.start,
           BTOR_COUNT_STACK (body),
           sizeof (BtorNode *),
           btor_cmp_node_id);

  while (!BTOR_EMPTY_STACK (body))
  {
    cur = BTOR_POP_STACK (body);

    // FIXME: better detection of local and non-local expressions
    if (cur->parameterized)
      BTOR_PUSH_STACK (mm, local, cur);
    else
      BTOR_PUSH_STACK (mm, non_local, cur);
  }

  /* dump expressions that are not local in 'fun' */
  while (!BTOR_EMPTY_STACK (non_local))
  {
    cur = BTOR_POP_STACK (non_local);
    assert (BTOR_IS_REGULAR_NODE (cur));
    assert (!cur->parameterized);
    dump_fun_let_smt2 (sdc, cur);
  }

  /* dump function signature */
  fputs ("(define-fun ", sdc->file);
  btor_dump_smt_id (sdc, fun);
  fputs (" (", sdc->file);

  init_lambda_iterator (&it, fun);
  while (has_next_lambda_iterator (&it))
  {
    cur   = next_lambda_iterator (&it);
    param = (BtorNode *) BTOR_LAMBDA_GET_PARAM (cur);
    btor_insert_in_ptr_hash_table (sdc->mark, cur);
    btor_insert_in_ptr_hash_table (sdc->mark, param);

    fputc ('(', sdc->file);
    btor_dump_smt_id (sdc, param);
    fputc (' ', sdc->file);
    dump_sort_smt2 (sdc, param);
    fputc (')', sdc->file);
  }
  fputs (") ", sdc->file);

  dump_sort_smt2 (sdc, fun);
  fputc ('\n', sdc->file);

  /* dump expressions that are local in 'fun' */
  lets = 0;
  while (!BTOR_EMPTY_STACK (local))
  {
    cur = BTOR_POP_STACK (local);
    assert (BTOR_IS_REGULAR_NODE (cur));
    assert (cur->parameterized);

    fputc (' ', sdc->file);
    dump_let_smt2 (sdc, cur);
    lets++;
  }

  fputc (' ', sdc->file);
  if (lets == 0)
  {
    cur = BTOR_LAMBDA_GET_BODY (fun);
    assert (btor_find_in_ptr_hash_table (sdc->mark, BTOR_REAL_ADDR_NODE (cur)));
  }

  /* innermost expression */
  btor_dump_smt_id (sdc, cur);

  /* close lets */
  for (i = 0; i < lets; i++) fputc (')', sdc->file);

  /* close define-fun */
  fputs (")\n", sdc->file);

  BTOR_RELEASE_STACK (mm, local);
  BTOR_RELEASE_STACK (mm, non_local);
  BTOR_RELEASE_STACK (mm, body);
  BTOR_RELEASE_STACK (mm, visit);
  btor_delete_ptr_hash_table (mark);
}

static void
dump_var_smt2 (BtorSMTDumpContext *sdc, BtorNode *exp)
{
  assert (!btor_find_in_ptr_hash_table (sdc->mark, exp));
  dump_declare_fun_smt2 (sdc, exp);
  btor_insert_in_ptr_hash_table (sdc->mark, exp);
}

static void
dump_const_smt2 (BtorSMTDumpContext *sdc, BtorNode *exp)
{
  assert (BTOR_IS_REGULAR_NODE (exp));
  assert (!btor_find_in_ptr_hash_table (sdc->mark, exp));

  char *val;
  val = btor_const_to_decimal (sdc->btor->mm, exp->bits);

  fputs ("(define-fun ", sdc->file);
  btor_dump_smt_id (sdc, exp);
  fprintf (sdc->file, " () ");
  dump_sort_smt2 (sdc, exp);
  fprintf (sdc->file, " (_ bv%s %d))\n", val, exp->len);
  btor_freestr (sdc->btor->mm, val);
  btor_insert_in_ptr_hash_table (sdc->mark, exp);
}

static void
dump_assert_smt2 (BtorSMTDumpContext *sdc, BtorNode *exp)
{
  assert (sdc);
  assert (exp);
  assert (BTOR_REAL_ADDR_NODE (exp)->len == 1);
  assert (btor_find_in_ptr_hash_table (sdc->mark, BTOR_REAL_ADDR_NODE (exp)));

  // FIXME: for now we have to assert root != 0 in order to get a boolean
  //        expression for assert
  fputs ("(assert (not (= ", sdc->file);
  btor_dump_smt_id (sdc, exp);
  fputs (" #b0)))\n", sdc->file);
}

static void
dump_smt2 (BtorSMTDumpContext *sdc)
{
  assert (sdc);

  int i, j;
  BtorNode *e, *cur;
  BtorMemMgr *mm;
  BtorNodePtrStack visit, consts, vars, arrays, funs, rem;
  BtorPtrHashTable *roots;

  mm = sdc->btor->mm;
  BTOR_INIT_STACK (visit);
  BTOR_INIT_STACK (rem);
  BTOR_INIT_STACK (consts);
  BTOR_INIT_STACK (vars);
  BTOR_INIT_STACK (arrays);
  BTOR_INIT_STACK (funs);

  roots = btor_new_ptr_hash_table (mm,
                                   (BtorHashPtr) btor_hash_exp_by_id,
                                   (BtorCmpPtr) btor_compare_exp_by_id);

  for (i = 0; i < BTOR_COUNT_STACK (sdc->roots); i++)
  {
    cur = BTOR_REAL_ADDR_NODE (BTOR_PEEK_STACK (sdc->roots, i));
    if (btor_find_in_ptr_hash_table (roots, cur)) continue;

    assert (!btor_find_in_ptr_hash_table (sdc->mark, cur));
    BTOR_PUSH_STACK (mm, visit, cur);
    btor_insert_in_ptr_hash_table (roots, cur);
  }

  /* collect constants, variables, array variables and functions */
  while (!BTOR_EMPTY_STACK (visit))
  {
    cur = BTOR_POP_STACK (visit);
    assert (BTOR_IS_REGULAR_NODE (cur));

    if (btor_find_in_ptr_hash_table (sdc->dump, cur)) continue;

    /* mark all nodes that need to be dumped */
    if (!BTOR_IS_ARGS_NODE (cur))
    {
      btor_insert_in_ptr_hash_table (sdc->dump, cur);
      BTOR_PUSH_STACK (mm, rem, cur);
    }

    if (BTOR_IS_BV_CONST_NODE (cur))
      BTOR_PUSH_STACK (mm, consts, cur);
    else if (BTOR_IS_BV_VAR_NODE (cur))
      BTOR_PUSH_STACK (mm, vars, cur);
    else if (BTOR_IS_ARRAY_VAR_NODE (cur))
      BTOR_PUSH_STACK (mm, arrays, cur);
    else if (BTOR_IS_LAMBDA_NODE (cur) && !cur->parameterized
             && (!BTOR_IS_CURRIED_LAMBDA_NODE (cur)
                 || BTOR_IS_FIRST_CURRIED_LAMBDA (cur)))
      BTOR_PUSH_STACK (mm, funs, cur);

    for (j = 0; j < cur->arity; j++)
      BTOR_PUSH_STACK (mm, visit, BTOR_REAL_ADDR_NODE (cur->e[j]));
  }

  /* begin dump */
  if (BTOR_EMPTY_STACK (arrays))
    fputs ("(set-logic QF_BV)\n", sdc->file);
  else
    fputs ("(set-logic QF_AUFBV)\n", sdc->file);

  if (consts.start)
    qsort (consts.start, BTOR_COUNT_STACK (consts), sizeof e, btor_cmp_node_id);

  for (i = 0; i < BTOR_COUNT_STACK (consts); i++)
  {
    cur = BTOR_PEEK_STACK (consts, i);
    dump_const_smt2 (sdc, cur);
  }

  if (vars.start)
    qsort (vars.start, BTOR_COUNT_STACK (vars), sizeof e, btor_cmp_node_id);

  for (i = 0; i < BTOR_COUNT_STACK (vars); i++)
  {
    cur = BTOR_PEEK_STACK (vars, i);
    dump_var_smt2 (sdc, cur);
  }

  if (arrays.start)
    qsort (arrays.start, BTOR_COUNT_STACK (arrays), sizeof e, btor_cmp_node_id);

  for (i = 0; i < BTOR_COUNT_STACK (arrays); i++)
  {
    cur = BTOR_PEEK_STACK (arrays, i);
    dump_var_smt2 (sdc, cur);
  }

  if (funs.start)
    qsort (funs.start, BTOR_COUNT_STACK (funs), sizeof e, btor_cmp_node_id);

  for (i = 0; i < BTOR_COUNT_STACK (funs); i++)
  {
    cur = BTOR_PEEK_STACK (funs, i);
    dump_fun_smt2 (sdc, cur);
  }

  if (rem.start)
    qsort (rem.start, BTOR_COUNT_STACK (rem), sizeof e, btor_cmp_node_id);

  for (i = 0; i < BTOR_COUNT_STACK (rem); i++)
  {
    cur = BTOR_PEEK_STACK (rem, i);
    assert (BTOR_IS_REGULAR_NODE (cur));

    if (btor_find_in_ptr_hash_table (sdc->mark, cur)) continue;

    assert (!cur->parameterized);

    dump_fun_let_smt2 (sdc, cur);
  }

  for (i = 0; i < BTOR_COUNT_STACK (sdc->roots); i++)
  {
    cur = BTOR_PEEK_STACK (sdc->roots, i);
    dump_assert_smt2 (sdc, cur);
  }

#ifndef NDEBUG
  for (i = 0; i < BTOR_COUNT_STACK (rem); i++)
  {
    cur = BTOR_PEEK_STACK (rem, i);
    assert (btor_find_in_ptr_hash_table (sdc->mark, cur));
  }
#endif

  BTOR_RELEASE_STACK (mm, rem);
  BTOR_RELEASE_STACK (mm, visit);
  BTOR_RELEASE_STACK (mm, consts);
  BTOR_RELEASE_STACK (mm, vars);
  BTOR_RELEASE_STACK (mm, arrays);
  BTOR_RELEASE_STACK (mm, funs);
  btor_delete_ptr_hash_table (roots);

  fputs ("(check-sat)\n", sdc->file);
  fputs ("(exit)\n", sdc->file);
  fflush (sdc->file);
}

void
btor_dump_smt2_nodes (Btor *btor, FILE *file, BtorNode **roots, int nroots)
{
  assert (btor);
  assert (file);
  assert (roots);
  assert (nroots > 0);

  int i;
  BtorSMTDumpContext *sdc;

  sdc = new_smt_dump_context (btor, file);

  for (i = 0; i < nroots; i++) add_root_to_smt_dump_context (sdc, roots[i]);

  dump_smt2 (sdc);
  delete_smt_dump_context (sdc);
}

void
btor_dump_smt2 (Btor *btor, FILE *file)
{
  assert (btor);
  assert (file);
  assert (!btor->inc_enabled);
  //  assert (!btor->model_gen);

  int ret, nested_funs = 0;
  Btor *clone;
  BtorNode *temp;
  BtorHashTableIterator it;
  BtorSMTDumpContext *sdc;

  init_node_hash_table_iterator (&it, btor->lambdas);
  while (has_next_node_hash_table_iterator (&it))
  {
    if (next_node_hash_table_iterator (&it)->parameterized)
    {
      nested_funs = 1;
      break;
    }
  }

  if (nested_funs)
  {
    clone = btor_clone_btor (btor);
    // FIXME: do not beta reduce all lambdas, but eliminate nested ones (new
    //        function)
    btor_enable_beta_reduce_all (clone);
    btor = clone;
  }

  sdc = new_smt_dump_context (btor, file);
  ret = btor_simplify (btor);

  if (ret == BTOR_UNKNOWN)
  {
    init_node_hash_table_iterator (&it, btor->unsynthesized_constraints);
    while (has_next_node_hash_table_iterator (&it))
      add_root_to_smt_dump_context (sdc, next_node_hash_table_iterator (&it));
  }
  else
  {
    assert (ret == BTOR_SAT || ret == BTOR_UNSAT);
    temp = (ret == BTOR_SAT) ? btor_true_exp (btor) : btor_false_exp (btor);
    add_root_to_smt_dump_context (sdc, temp);
    btor_release_exp (btor, temp);
  }

  dump_smt2 (sdc);
  delete_smt_dump_context (sdc);

  if (nested_funs) btor_delete_btor (clone);
}
