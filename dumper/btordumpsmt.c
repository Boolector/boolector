/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2013 Armin Biere.
 *  Copyright (C) 2012-2013 Mathias Preiner.
 *  Copyright (C) 2012-2014 Aina Niemetz.
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
#include "btorsort.h"
#if !defined(NDEBUG) && defined(BTOR_ENABLE_CLONING)
#include "btorclone.h"
#endif

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
  int pretty_print;
  int version;
  int open_lets;
};

typedef struct BtorSMTDumpContext BtorSMTDumpContext;

static BtorSMTDumpContext *
new_smt_dump_context (Btor *btor, FILE *file, int version)
{
  assert (version == 1 || version == 2);
  BtorSMTDumpContext *sdc;
  BTOR_CNEW (btor->mm, sdc);

  sdc->btor         = btor;
  sdc->dump         = btor_new_ptr_hash_table (btor->mm,
                                       (BtorHashPtr) btor_hash_exp_by_id,
                                       (BtorCmpPtr) btor_compare_exp_by_id);
  sdc->mark         = btor_new_ptr_hash_table (btor->mm,
                                       (BtorHashPtr) btor_hash_exp_by_id,
                                       (BtorCmpPtr) btor_compare_exp_by_id);
  sdc->idtab        = btor_new_ptr_hash_table (btor->mm,
                                        (BtorHashPtr) btor_hash_exp_by_id,
                                        (BtorCmpPtr) btor_compare_exp_by_id);
  sdc->file         = file;
  sdc->maxid        = 1;
  sdc->pretty_print = btor->options.pretty_print.val;
  sdc->version      = version;

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
cmp_node_id (const void *p, const void *q)
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

  if (sdc->pretty_print)
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
dump_smt_id (BtorSMTDumpContext *sdc, BtorNode *exp)
{
  assert (sdc);
  assert (exp);

  const char *type, *sym;
  BtorNode *u;

  u = BTOR_REAL_ADDR_NODE (exp);

  if (u != exp) fputs ("(bvnot ", sdc->file);

  switch (u->kind)
  {
    case BTOR_BV_VAR_NODE: type = "v"; goto VAR_PARAM_NODE;

    case BTOR_PARAM_NODE:
      type = "p";
    VAR_PARAM_NODE:
      sym = btor_get_symbol_exp (sdc->btor, u);
      if (sym && !isdigit (sym[0]))
      {
        fputs (sym, sdc->file);
        goto CLOSE;
      }
      break;

    case BTOR_UF_NODE: type = BTOR_IS_UF_ARRAY_NODE (u) ? "a" : "uf"; break;

    case BTOR_LAMBDA_NODE: type = "f"; break;

    default: type = sdc->version == 1 ? "?e" : "$e";
  }

  fprintf (sdc->file, "%s%d", type, smt_id (sdc, u));

CLOSE:
  if (u != exp) fputc (')', sdc->file);
}

static void
dump_bit_smt (BtorSMTDumpContext *sdc, int bit)
{
  assert (bit == 0 || bit == 1);

  const char *fmt;
  fmt = sdc->version == 1 ? "bv%d[1]" : "#b%d";
  fprintf (sdc->file, fmt, bit);
}

static void
dump_sort_smt_aux (BtorSMTDumpContext *sdc, BtorSort *sort)
{
  int i;
  const char *fmt;

  switch (sort->kind)
  {
    case BTOR_BOOL_SORT: fputs ("Bool", sdc->file); break;

    case BTOR_BITVEC_SORT:
      fmt = sdc->version == 1 ? "BitVec[%d]" : "(_ BitVec %d)";
      fprintf (sdc->file, fmt, sort->bitvec.len);
      break;

    case BTOR_ARRAY_SORT:
      fmt = sdc->version == 1 ? "Array[%d:%d]"
                              : "(Array (_ BitVec %d) (_ BitVec %d))";
      assert (sort->array.index->kind == BTOR_BITVEC_SORT);
      assert (sort->array.element->kind == BTOR_BITVEC_SORT);
      fprintf (sdc->file,
               fmt,
               sort->array.index->bitvec.len,
               sort->array.element->bitvec.len);
      break;

    case BTOR_FUN_SORT:
      /* print domain */
      if (sdc->version == 2) fputc ('(', sdc->file);
      if (sort->fun.domain->kind == BTOR_TUPLE_SORT)
      {
        for (i = 0; i < sort->fun.domain->tuple.num_elements; i++)
        {
          dump_sort_smt_aux (sdc, sort->fun.domain->tuple.elements[i]);
          if (i < sort->fun.domain->tuple.num_elements - 1)
            fputc (' ', sdc->file);
        }
      }
      else
        dump_sort_smt_aux (sdc, sort->fun.domain);
      if (sdc->version == 2) fputc (')', sdc->file);
      fputc (' ', sdc->file);

      /* print co-domain */
      dump_sort_smt_aux (sdc, sort->fun.codomain);
      break;

    default: assert (0);
  }
}

static void
dump_sort_smt (BtorSMTDumpContext *sdc, BtorNode *exp)
{
  assert (sdc);
  assert (exp);

  BtorSort *sort, tmp, index, element;

  exp = BTOR_REAL_ADDR_NODE (exp);

  if (BTOR_IS_UF_NODE (exp))
    sort = ((BtorUFNode *) exp)->sort;
  else if (BTOR_IS_UF_ARRAY_NODE (exp))
  {
    index.kind         = BTOR_BITVEC_SORT;
    index.bitvec.len   = BTOR_ARRAY_INDEX_LEN (exp);
    element.kind       = BTOR_BITVEC_SORT;
    element.bitvec.len = exp->len;
    tmp.kind           = BTOR_ARRAY_SORT;
    tmp.array.index    = &index;
    tmp.array.element  = &element;
    sort               = &tmp;
  }
  else
  {
    tmp.kind       = BTOR_BITVEC_SORT;
    tmp.bitvec.len = exp->len;
    sort           = &tmp;
  }
  dump_sort_smt_aux (sdc, sort);
}

static void
dump_exp_smt (BtorSMTDumpContext *sdc, BtorNode *exp)
{
  assert (sdc);
  assert (exp);
  assert (!btor_find_in_ptr_hash_table (sdc->mark, exp));

  int pad, i;
  char *val;
  const char *op, *fmt;
  BtorNode *arg;
  BtorMemMgr *mm;
  BtorArgsIterator it;

  mm = sdc->btor->mm;

  switch (exp->kind)
  {
    case BTOR_BV_CONST_NODE:
      val = btor_const_to_decimal (mm, exp->bits);
      fmt = sdc->version == 1 ? "bv%s[%d]" : "(_ bv%s %d)";
      fprintf (sdc->file, fmt, val, exp->len);
      btor_freestr (mm, val);
      break;

    case BTOR_SLICE_NODE:
      fmt = sdc->version == 1 ? "(extract[%d:%d] " : "((_ extract %d %d) ";
      fprintf (sdc->file, fmt, exp->upper, exp->lower);
      dump_smt_id (sdc, exp->e[0]);
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
      dump_smt_id (sdc, exp->e[0]);
      fputc (' ', sdc->file);

      assert (exp->len > 1);
      pad = exp->len - BTOR_REAL_ADDR_NODE (exp->e[1])->len;

      fmt = sdc->version == 1 ? " (zero_extend[%d] " : " ((_ zero_extend %d) ";
      fprintf (sdc->file, fmt, pad);

      dump_smt_id (sdc, exp->e[1]);
      fputs ("))", sdc->file);
      break;

    case BTOR_BCOND_NODE:
      fputs ("(ite (= ", sdc->file);
      dump_bit_smt (sdc, 1);
      fputc (' ', sdc->file);
      dump_smt_id (sdc, exp->e[0]);
      fputs (") ", sdc->file);
      dump_smt_id (sdc, exp->e[1]);
      fputc (' ', sdc->file);
      dump_smt_id (sdc, exp->e[2]);
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
      dump_smt_id (sdc, exp->e[0]);
      fputc (' ', sdc->file);
      dump_smt_id (sdc, exp->e[1]);
      fputs (") ", sdc->file);
      dump_bit_smt (sdc, 1);
      fputc (' ', sdc->file);
      dump_bit_smt (sdc, 0);
      fputc (')', sdc->file);
      break;

    case BTOR_APPLY_NODE:
      fputc ('(', sdc->file);
      /* array select */
      if (BTOR_IS_UF_ARRAY_NODE (exp->e[0]))
      {
        fputs ("select ", sdc->file);
        dump_smt_id (sdc, exp->e[0]);
        fputc (' ', sdc->file);
        assert (BTOR_IS_REGULAR_NODE (exp->e[1]));
        assert (((BtorArgsNode *) exp->e[1])->num_args == 1);
        dump_smt_id (sdc, exp->e[1]->e[0]);
      }
      /* function application */
      else
      {
        dump_smt_id (sdc, exp->e[0]);

        init_args_iterator (&it, exp->e[1]);
        while (has_next_args_iterator (&it))
        {
          arg = next_args_iterator (&it);
          fputc (' ', sdc->file);
          dump_smt_id (sdc, arg);
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
        dump_smt_id (sdc, exp->e[i]);
      }

      fputc (')', sdc->file);
  }
  btor_insert_in_ptr_hash_table (sdc->mark, exp);
}

static void
dump_let_smt (BtorSMTDumpContext *sdc, BtorNode *exp)
{
  assert (sdc);
  assert (BTOR_IS_REGULAR_NODE (exp));

  if (sdc->version == 1)
  {
    fputs ("(let (", sdc->file);
    dump_smt_id (sdc, exp);
    fputc (' ', sdc->file);
    dump_exp_smt (sdc, exp);
    fputs (")\n", sdc->file);
  }
  else
  {
    fputs ("(let ((", sdc->file);
    dump_smt_id (sdc, exp);
    fputc (' ', sdc->file);
    dump_exp_smt (sdc, exp);
    fputs ("))", sdc->file);
  }
  sdc->open_lets++;
}

static void
dump_fun_let_smt2 (BtorSMTDumpContext *sdc, BtorNode *exp)
{
  assert (sdc);
  assert (sdc->version == 2);
  assert (BTOR_IS_REGULAR_NODE (exp));

  if (btor_find_in_ptr_hash_table (sdc->mark, exp)) return;

  fputs ("(define-fun ", sdc->file);
  dump_smt_id (sdc, exp);
  fputs (" () ", sdc->file);
  dump_sort_smt (sdc, exp);
  fputc (' ', sdc->file);
  dump_exp_smt (sdc, exp);
  fputs (")\n", sdc->file);
}

static void
dump_fun_smt2 (BtorSMTDumpContext *sdc, BtorNode *fun)
{
  assert (fun);
  assert (sdc);
  assert (sdc->version == 2);
  assert (BTOR_IS_REGULAR_NODE (fun));
  assert (BTOR_IS_FUN_NODE (fun));
  assert (!fun->parameterized);
  assert (!btor_find_in_ptr_hash_table (sdc->mark, fun));

  int i;
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
    qsort (
        body.start, BTOR_COUNT_STACK (body), sizeof (BtorNode *), cmp_node_id);

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
  dump_smt_id (sdc, fun);
  fputs (" (", sdc->file);

  init_lambda_iterator (&it, fun);
  while (has_next_lambda_iterator (&it))
  {
    cur   = next_lambda_iterator (&it);
    param = (BtorNode *) BTOR_LAMBDA_GET_PARAM (cur);
    btor_insert_in_ptr_hash_table (sdc->mark, cur);
    btor_insert_in_ptr_hash_table (sdc->mark, param);

    fputc ('(', sdc->file);
    dump_smt_id (sdc, param);
    fputc (' ', sdc->file);
    dump_sort_smt (sdc, param);
    fputc (')', sdc->file);
  }
  fputs (") ", sdc->file);

  dump_sort_smt (sdc, fun);
  fputc ('\n', sdc->file);

  assert (sdc->open_lets == 0);
  /* dump expressions that are local in 'fun' */
  while (!BTOR_EMPTY_STACK (local))
  {
    cur = BTOR_POP_STACK (local);
    assert (BTOR_IS_REGULAR_NODE (cur));
    assert (cur->parameterized);

    fputc (' ', sdc->file);
    dump_let_smt (sdc, cur);
  }

  fputc (' ', sdc->file);
  if (sdc->open_lets == 0)
  {
    cur = BTOR_LAMBDA_GET_BODY (fun);
    assert (btor_find_in_ptr_hash_table (sdc->mark, BTOR_REAL_ADDR_NODE (cur)));
  }

  /* innermost expression */
  dump_smt_id (sdc, cur);

  /* close lets */
  for (i = 0; i < sdc->open_lets; i++) fputc (')', sdc->file);
  sdc->open_lets = 0;

  /* close define-fun */
  fputs (")\n", sdc->file);

  BTOR_RELEASE_STACK (mm, local);
  BTOR_RELEASE_STACK (mm, non_local);
  BTOR_RELEASE_STACK (mm, body);
  BTOR_RELEASE_STACK (mm, visit);
  btor_delete_ptr_hash_table (mark);
}

static void
dump_declare_fun_smt (BtorSMTDumpContext *sdc, BtorNode *exp)
{
  assert (!btor_find_in_ptr_hash_table (sdc->mark, exp));
  if (sdc->version == 1)
  {
    fputs (":extrafuns ((", sdc->file);
    dump_smt_id (sdc, exp);
    fputs (" ", sdc->file);
    dump_sort_smt (sdc, exp);
    fputs ("))\n", sdc->file);
  }
  else
  {
    fputs ("(declare-fun ", sdc->file);
    dump_smt_id (sdc, exp);
    fputc (' ', sdc->file);
    if (BTOR_IS_BV_VAR_NODE (exp) || BTOR_IS_UF_ARRAY_NODE (exp))
      fputs ("() ", sdc->file);
    dump_sort_smt (sdc, exp);
    fputs (")\n", sdc->file);
  }
  btor_insert_in_ptr_hash_table (sdc->mark, exp);
}

static void
dump_const_smt (BtorSMTDumpContext *sdc, BtorNode *exp)
{
  assert (BTOR_IS_REGULAR_NODE (exp));
  assert (!btor_find_in_ptr_hash_table (sdc->mark, exp));

  if (sdc->version == 1)
    dump_let_smt (sdc, exp);
  else
    dump_fun_let_smt2 (sdc, exp);
}

static void
dump_assert_smt2 (BtorSMTDumpContext *sdc, BtorNode *exp)
{
  assert (sdc);
  assert (sdc->version == 2);
  assert (exp);
  assert (BTOR_REAL_ADDR_NODE (exp)->len == 1);
  assert (btor_find_in_ptr_hash_table (sdc->mark, BTOR_REAL_ADDR_NODE (exp)));

  // FIXME: for now we have to assert root != 0 in order to get a boolean
  //        expression for assert
  fputs ("(assert (not (= ", sdc->file);
  dump_smt_id (sdc, exp);
  fputs (" #b0)))\n", sdc->file);
}

static void
set_logic_smt (BtorSMTDumpContext *sdc, const char *logic)
{
  assert (sdc);

  const char *fmt;

  fmt = sdc->version == 1 ? ":logic %s\n" : "(set-logic %s)\n";
  fprintf (sdc->file, fmt, logic);
}

#define WRAP_NON_BOOL_ROOT(e)                                        \
  do                                                                 \
  {                                                                  \
    assert (sdc->version == 1);                                      \
    fputs ("(not (= ", sdc->file);                                   \
    dump_smt_id (sdc, e);                                            \
    fprintf (sdc->file, " bv0[%d]))", BTOR_REAL_ADDR_NODE (e)->len); \
  } while (0)

static void
dump_smt (BtorSMTDumpContext *sdc)
{
  assert (sdc);

  int i, j;
  BtorNode *e, *cur;
  BtorMemMgr *mm;
  BtorNodePtrStack visit, consts, vars, arrays, funs, rem, ufs;
  BtorPtrHashTable *roots;

  mm = sdc->btor->mm;
  BTOR_INIT_STACK (visit);
  BTOR_INIT_STACK (rem);
  BTOR_INIT_STACK (consts);
  BTOR_INIT_STACK (vars);
  BTOR_INIT_STACK (arrays);
  BTOR_INIT_STACK (funs);
  BTOR_INIT_STACK (ufs);

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
    else if (BTOR_IS_UF_ARRAY_NODE (cur))
      BTOR_PUSH_STACK (mm, arrays, cur);
    else if (BTOR_IS_UF_NODE (cur))
      BTOR_PUSH_STACK (mm, ufs, cur);
    else if (BTOR_IS_LAMBDA_NODE (cur) && !cur->parameterized
             && (!BTOR_IS_CURRIED_LAMBDA_NODE (cur)
                 || BTOR_IS_FIRST_CURRIED_LAMBDA (cur)))
      BTOR_PUSH_STACK (mm, funs, cur);

    for (j = 0; j < cur->arity; j++)
      BTOR_PUSH_STACK (mm, visit, BTOR_REAL_ADDR_NODE (cur->e[j]));
  }

  /* begin dump */
  if (sdc->version == 1) fputs ("(benchmark dump\n", sdc->file);

  if (BTOR_EMPTY_STACK (arrays) && BTOR_EMPTY_STACK (ufs))
    set_logic_smt (sdc, "QF_BV");
  else if (BTOR_EMPTY_STACK (arrays))
    set_logic_smt (sdc, "QF_UFBV");
  else
    set_logic_smt (sdc, "QF_AUFBV");

  if (vars.start)
    qsort (vars.start, BTOR_COUNT_STACK (vars), sizeof e, cmp_node_id);

  for (i = 0; i < BTOR_COUNT_STACK (vars); i++)
  {
    cur = BTOR_PEEK_STACK (vars, i);
    dump_declare_fun_smt (sdc, cur);
  }

  if (ufs.start)
    qsort (ufs.start, BTOR_COUNT_STACK (ufs), sizeof e, cmp_node_id);

  for (i = 0; i < BTOR_COUNT_STACK (ufs); i++)
  {
    cur = BTOR_PEEK_STACK (ufs, i);
    dump_declare_fun_smt (sdc, cur);
  }

  if (arrays.start)
    qsort (arrays.start, BTOR_COUNT_STACK (arrays), sizeof e, cmp_node_id);

  for (i = 0; i < BTOR_COUNT_STACK (arrays); i++)
  {
    cur = BTOR_PEEK_STACK (arrays, i);
    dump_declare_fun_smt (sdc, cur);
  }

  if (sdc->version == 1) fputs (":formula\n", sdc->file);

  if (consts.start)
    qsort (consts.start, BTOR_COUNT_STACK (consts), sizeof e, cmp_node_id);

  for (i = 0; i < BTOR_COUNT_STACK (consts); i++)
  {
    cur = BTOR_PEEK_STACK (consts, i);
    dump_const_smt (sdc, cur);
  }

  if (funs.start)
    qsort (funs.start, BTOR_COUNT_STACK (funs), sizeof e, cmp_node_id);

  for (i = 0; i < BTOR_COUNT_STACK (funs); i++)
  {
    cur = BTOR_PEEK_STACK (funs, i);
    dump_fun_smt2 (sdc, cur);
  }

  if (rem.start)
    qsort (rem.start, BTOR_COUNT_STACK (rem), sizeof e, cmp_node_id);

  for (i = 0; i < BTOR_COUNT_STACK (rem); i++)
  {
    cur = BTOR_PEEK_STACK (rem, i);
    assert (BTOR_IS_REGULAR_NODE (cur));

    if (btor_find_in_ptr_hash_table (sdc->mark, cur)) continue;

    assert (!cur->parameterized);

    if (sdc->version == 1)
      dump_let_smt (sdc, cur);
    else
      dump_fun_let_smt2 (sdc, cur);
  }

  /* build root */
  if (sdc->version == 1)
  {
    int open_left_par = 0;
    for (i = 0; i < BTOR_COUNT_STACK (sdc->roots) - 1; i++)
    {
      e = BTOR_PEEK_STACK (sdc->roots, i);
      fputs (" (and ", sdc->file);
      WRAP_NON_BOOL_ROOT (e);
      open_left_par++;
    }
    fputc (' ', sdc->file);

    e = BTOR_TOP_STACK (sdc->roots);
    WRAP_NON_BOOL_ROOT (e);

    for (i = 0; i < open_left_par + 1 + sdc->open_lets; i++)
      fputc (')', sdc->file);

    fputc ('\n', sdc->file);
    sdc->open_lets = 0;
  }
  else
  {
    for (i = 0; i < BTOR_COUNT_STACK (sdc->roots); i++)
    {
      cur = BTOR_PEEK_STACK (sdc->roots, i);
      dump_assert_smt2 (sdc, cur);
    }
  }
  assert (sdc->open_lets == 0);

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
  BTOR_RELEASE_STACK (mm, ufs);
  btor_delete_ptr_hash_table (roots);

  if (sdc->version == 2)
  {
    fputs ("(check-sat)\n", sdc->file);
    fputs ("(exit)\n", sdc->file);
  }
  fflush (sdc->file);
}

static void
dump_smt_aux (Btor *btor, FILE *file, int version, BtorNode **roots, int nroots)
{
  assert (btor);
  assert (file);
  assert (version == 1 || version == 2);
  assert (!btor->options.incremental.val);
  //  assert (!btor->options.model_gen.val);

#if !defined(NDEBUG) && defined(BTOR_ENABLE_CLONING)
  Btor *clone;
  BtorNode *old, *new;
#endif
  int i, ret, nested_funs = 0;
  BtorNode *temp, *tmp_roots[nroots];
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

  for (i = 0; i < nroots; i++) tmp_roots[i] = roots[i];

  if (nested_funs || version == 1)
  {
#if !defined(NDEBUG) && defined(BTOR_ENABLE_CLONING)
    clone = btor_clone_exp_layer (btor, 0, 0);
    btor_set_opt (clone, BTOR_OPT_AUTO_CLEANUP, 1);

    /* update roots if already added */
    for (i = 0; i < nroots; i++)
    {
      old = tmp_roots[i];
      new = BTOR_PEEK_STACK (clone->nodes_id_table,
                             BTOR_REAL_ADDR_NODE (old)->id);
      assert (new);
      assert (new != BTOR_REAL_ADDR_NODE (old));
      tmp_roots[i] = BTOR_COND_INVERT_NODE (old, new);
    }
    btor = clone;
#endif
    // FIXME: do not beta reduce all lambdas, but eliminate nested ones (new
    //        function)
    btor_set_opt (btor, BTOR_OPT_BETA_REDUCE_ALL, 1);
  }

  sdc = new_smt_dump_context (btor, file, version);

  if (nroots)
  {
    for (i = 0; i < nroots; i++)
      add_root_to_smt_dump_context (sdc, tmp_roots[i]);
  }
  else
  {
    ret = btor_simplify (btor);

    if (ret == BTOR_UNKNOWN)
    {
      init_node_hash_table_iterator (&it, btor->unsynthesized_constraints);
      queue_node_hash_table_iterator (&it, btor->synthesized_constraints);
      queue_node_hash_table_iterator (&it, btor->embedded_constraints);
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
  }

  dump_smt (sdc);
  delete_smt_dump_context (sdc);

#if !defined(NDEBUG) && defined(BTOR_ENABLE_CLONING)
  /* delete clone */
  if (nested_funs) btor_delete_btor (btor);
#endif
}

void
btor_dump_smt1_nodes (Btor *btor, FILE *file, BtorNode **roots, int nroots)
{
  assert (btor);
  assert (file);
  assert (roots);
  assert (nroots > 0);
  dump_smt_aux (btor, file, 1, roots, nroots);
}

void
btor_dump_smt1 (Btor *btor, FILE *file)
{
  assert (btor);
  assert (file);
  dump_smt_aux (btor, file, 1, 0, 0);
}

void
btor_dump_smt2_nodes (Btor *btor, FILE *file, BtorNode **roots, int nroots)
{
  assert (btor);
  assert (file);
  assert (roots);
  assert (nroots > 0);
  dump_smt_aux (btor, file, 2, roots, nroots);
}

void
btor_dump_smt2 (Btor *btor, FILE *file)
{
  assert (btor);
  assert (file);
  dump_smt_aux (btor, file, 2, 0, 0);
}
