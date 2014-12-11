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
#ifndef NDEBUG
#include "btorclone.h"
#endif

#include <ctype.h>
#include <limits.h>

struct BtorSMTDumpContext
{
  Btor *btor;
  BtorPtrHashTable *dump;
  BtorPtrHashTable *mark;
  BtorPtrHashTable *stores;
  BtorPtrHashTable *idtab;
  BtorPtrHashTable *roots;
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

  sdc->btor   = btor;
  sdc->dump   = btor_new_ptr_hash_table (btor->mm,
                                       (BtorHashPtr) btor_hash_exp_by_id,
                                       (BtorCmpPtr) btor_compare_exp_by_id);
  sdc->mark   = btor_new_ptr_hash_table (btor->mm,
                                       (BtorHashPtr) btor_hash_exp_by_id,
                                       (BtorCmpPtr) btor_compare_exp_by_id);
  sdc->stores = btor_new_ptr_hash_table (btor->mm,
                                         (BtorHashPtr) btor_hash_exp_by_id,
                                         (BtorCmpPtr) btor_compare_exp_by_id);
  sdc->idtab  = btor_new_ptr_hash_table (btor->mm,
                                        (BtorHashPtr) btor_hash_exp_by_id,
                                        (BtorCmpPtr) btor_compare_exp_by_id);
  /* use pointer for hashing and comparison */
  sdc->roots        = btor_new_ptr_hash_table (btor->mm, 0, 0);
  sdc->file         = file;
  sdc->maxid        = 1;
  sdc->pretty_print = btor->options.pretty_print.val;
  sdc->version      = version;
  return sdc;
}

static void
delete_smt_dump_context (BtorSMTDumpContext *sdc)
{
  BtorHashTableIterator it;

  btor_delete_ptr_hash_table (sdc->dump);
  btor_delete_ptr_hash_table (sdc->mark);
  btor_delete_ptr_hash_table (sdc->stores);
  btor_delete_ptr_hash_table (sdc->idtab);

  init_node_hash_table_iterator (&it, sdc->roots);
  while (has_next_node_hash_table_iterator (&it))
    btor_release_exp (sdc->btor, next_node_hash_table_iterator (&it));
  btor_delete_ptr_hash_table (sdc->roots);

  BTOR_DELETE (sdc->btor->mm, sdc);
}

static void
add_root_to_smt_dump_context (BtorSMTDumpContext *sdc, BtorNode *root)
{
  if (!btor_find_in_ptr_hash_table (sdc->roots, root))
    btor_insert_in_ptr_hash_table (sdc->roots, btor_copy_exp (sdc->btor, root));
}

static int
is_root (BtorSMTDumpContext *sdc, BtorNode *exp)
{
  return btor_find_in_ptr_hash_table (sdc->roots, exp)
         || btor_find_in_ptr_hash_table (sdc->roots, BTOR_INVERT_NODE (exp));
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
    case BTOR_BV_VAR_NODE: type = "v"; goto DUMP_SYMBOL;

    case BTOR_PARAM_NODE:
      type = "p";
    DUMP_SYMBOL:
      sym = btor_get_symbol_exp (sdc->btor, u);
      if (sym && !isdigit (sym[0]))
      {
        fputs (sym, sdc->file);
        goto CLOSE;
      }
      break;

    case BTOR_UF_NODE:
      type = BTOR_IS_UF_ARRAY_NODE (u) ? "a" : "uf";
      goto DUMP_SYMBOL;

    case BTOR_LAMBDA_NODE: type = "f"; goto DUMP_SYMBOL;

    default: type = sdc->version == 1 ? "?e" : "$e";
  }

  fprintf (sdc->file, "%s%d", type, smt_id (sdc, u));

CLOSE:
  if (u != exp) fputc (')', sdc->file);
}

// TODO: remove format again?
static void
dump_const_value_smt (BtorSMTDumpContext *sdc, const char *bits, int format)
{
  assert (sdc);
  assert (bits);
  assert (format == BTOR_OUTPUT_BASE_BIN || format == BTOR_OUTPUT_BASE_DEC
          || format == BTOR_OUTPUT_BASE_HEX);

  char *val;
  const char *fmt;

  /* SMT-LIB v1.2 only supports decimal output */
  if (format == BTOR_OUTPUT_BASE_DEC || sdc->version == 1)
  {
    val = btor_const_to_decimal (sdc->btor->mm, bits);
    fmt = sdc->version == 1 ? "bv%s[%d]" : "(_ bv%s %d)";
    fprintf (sdc->file, fmt, val, strlen (bits));
    btor_freestr (sdc->btor->mm, val);
  }
  else if (format == BTOR_OUTPUT_BASE_HEX && strlen (bits) % 4 == 0)
  {
    assert (sdc->version == 2);
    val = btor_const_to_hex (sdc->btor->mm, bits);
    fprintf (sdc->file, "#x%s", val);
    btor_freestr (sdc->btor->mm, val);
  }
  else
  {
    assert (sdc->version == 2);
    fprintf (sdc->file, "#b%s", bits);
  }
}

void
btor_dump_sort_smt (BtorSort *sort, int version, FILE *file)
{
  int i;
  const char *fmt;

  switch (sort->kind)
  {
    case BTOR_BOOL_SORT: fputs ("Bool", file); break;

    case BTOR_BITVEC_SORT:
      fmt = version == 1 ? "BitVec[%d]" : "(_ BitVec %d)";
      fprintf (file, fmt, sort->bitvec.len);
      break;

    case BTOR_ARRAY_SORT:
      fmt =
          version == 1 ? "Array[%d:%d]" : "(Array (_ BitVec %d) (_ BitVec %d))";
      assert (sort->array.index->kind == BTOR_BITVEC_SORT);
      assert (sort->array.element->kind == BTOR_BITVEC_SORT);
      fprintf (file,
               fmt,
               sort->array.index->bitvec.len,
               sort->array.element->bitvec.len);
      break;

    case BTOR_FUN_SORT:
      /* print domain */
      if (version == 2) fputc ('(', file);
      if (sort->fun.domain->kind == BTOR_TUPLE_SORT)
      {
        for (i = 0; i < sort->fun.domain->tuple.num_elements; i++)
        {
          btor_dump_sort_smt (
              sort->fun.domain->tuple.elements[i], version, file);
          if (i < sort->fun.domain->tuple.num_elements - 1) fputc (' ', file);
        }
      }
      else
        btor_dump_sort_smt (sort->fun.domain, version, file);
      if (version == 2) fputc (')', file);
      fputc (' ', file);

      /* print co-domain */
      btor_dump_sort_smt (sort->fun.codomain, version, file);
      break;

    default: assert (0);
  }
}

void
btor_dump_sort_smt_node (BtorNode *exp, int version, FILE *file)
{
  assert (exp);
  assert (version);
  assert (file);

  BtorSort *sort, tmp, index, element;

  exp = BTOR_REAL_ADDR_NODE (exp);

  if (BTOR_IS_UF_ARRAY_NODE (exp))
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
  else if (BTOR_IS_UF_NODE (exp))
    sort = ((BtorUFNode *) exp)->sort;
  else
  {
    tmp.kind       = BTOR_BITVEC_SORT;
    tmp.bitvec.len = exp->len;
    sort           = &tmp;
  }
  btor_dump_sort_smt (sort, version, file);
}

static void
extract_store (BtorSMTDumpContext *sdc,
               BtorNode *exp,
               BtorNode **index,
               BtorNode **value,
               BtorNode **array)
{
  BtorNode *ite, *eq, *apply;

  if (!BTOR_IS_LAMBDA_NODE (exp)) return;

  if (((BtorLambdaNode *) exp)->num_params != 1) return;

  if (!BTOR_IS_BV_COND_NODE (BTOR_REAL_ADDR_NODE (exp->e[1]))) return;

  ite = exp->e[1];
  if (BTOR_IS_INVERTED_NODE (ite)) return;

  if (!BTOR_IS_BV_EQ_NODE (BTOR_REAL_ADDR_NODE (ite->e[0]))) return;

  /* check ite condition */
  eq = ite->e[0];
  if (BTOR_IS_INVERTED_NODE (eq)) return;

  if (!eq->parameterized) return;

  /* check if branch */
  if (BTOR_REAL_ADDR_NODE (ite->e[1])->parameterized) return;

  /* check else branch */
  if (!BTOR_REAL_ADDR_NODE (ite->e[2])->parameterized) return;

  if (!BTOR_IS_APPLY_NODE (BTOR_REAL_ADDR_NODE (ite->e[2]))) return;

  apply = ite->e[2];
  if (BTOR_IS_INVERTED_NODE (apply)) return;

  if (!BTOR_IS_UF_ARRAY_NODE (apply->e[0])
      && !btor_find_in_ptr_hash_table (sdc->stores, apply->e[0]))
    return;

  if (!BTOR_IS_PARAM_NODE (BTOR_REAL_ADDR_NODE (apply->e[1]->e[0]))) return;

  *index = BTOR_REAL_ADDR_NODE (eq->e[0])->parameterized ? eq->e[1] : eq->e[0];
  *value = ite->e[1];
  *array = apply->e[0];
}

#define DUMP_EXP_SMT(e)                                      \
  do                                                         \
  {                                                          \
    if (sdc->version == 1)                                   \
      dump_smt_id (sdc, e);                                  \
    else                                                     \
      recursively_dump_exp_smt (sdc, e, depth, depth_limit); \
  } while (0)

static void
recursively_dump_exp_smt (BtorSMTDumpContext *sdc,
                          BtorNode *exp,
                          int depth,
                          int depth_limit)
{
  assert (sdc);
  assert (exp);
  assert (btor_find_in_ptr_hash_table (sdc->dump, BTOR_REAL_ADDR_NODE (exp)));
  assert (sdc->version > 1 || BTOR_IS_REGULAR_NODE (exp));

  int pad, i;
  char *inv_bits;
  const char *op, *fmt;
  BtorNode *arg, *real_exp, *index = 0, *value = 0, *array = 0;
  BtorArgsIterator it;

  real_exp = BTOR_REAL_ADDR_NODE (exp);

  if (btor_find_in_ptr_hash_table (sdc->mark, real_exp))
  {
#ifndef NDEBUG
    BtorPtrHashBucket *b;
    assert (!BTOR_IS_BV_CONST_NODE (real_exp));
    b = btor_find_in_ptr_hash_table (sdc->dump, real_exp);
    assert (b);
    /* functions and variables are declared separately */
    assert (BTOR_IS_FUN_NODE (real_exp) || BTOR_IS_BV_VAR_NODE (real_exp)
            || b->data.asInt > 1);
#endif
    dump_smt_id (sdc, exp);
    return;
  }

  /* constants are inverted directly */
  if (BTOR_IS_INVERTED_NODE (exp) && !BTOR_IS_BV_CONST_NODE (real_exp))
    fputs ("(bvnot ", sdc->file);

  switch (real_exp->kind)
  {
    case BTOR_BV_CONST_NODE:
      if (BTOR_IS_INVERTED_NODE (exp))
      {
        inv_bits = btor_not_const (sdc->btor->mm, real_exp->bits);
        dump_const_value_smt (
            sdc, inv_bits, sdc->btor->options.output_number_format.val);
        btor_freestr (sdc->btor->mm, inv_bits);
      }
      else
        dump_const_value_smt (
            sdc, real_exp->bits, sdc->btor->options.output_number_format.val);
      break;

    case BTOR_SLICE_NODE:
      fmt = sdc->version == 1 ? "(extract[%d:%d] " : "((_ extract %d %d) ";
      fprintf (sdc->file, fmt, real_exp->upper, real_exp->lower);
      DUMP_EXP_SMT (real_exp->e[0]);
      fputc (')', sdc->file);
      break;

    case BTOR_SLL_NODE:
    case BTOR_SRL_NODE:
      fputc ('(', sdc->file);

      if (real_exp->kind == BTOR_SRL_NODE)
        fputs ("bvlshr", sdc->file);
      else
        fputs ("bvshl", sdc->file);

      fputc (' ', sdc->file);
      DUMP_EXP_SMT (real_exp->e[0]);
      fputc (' ', sdc->file);

      assert (real_exp->len > 1);
      pad = real_exp->len - BTOR_REAL_ADDR_NODE (real_exp->e[1])->len;

      fmt = sdc->version == 1 ? " (zero_extend[%d] " : " ((_ zero_extend %d) ";
      fprintf (sdc->file, fmt, pad);

      DUMP_EXP_SMT (real_exp->e[1]);
      fputs ("))", sdc->file);
      break;

    // TODO (ma): do not wrap condition if not required (if eq, ult, bool)
    case BTOR_BCOND_NODE:
      fputs ("(ite (= ", sdc->file);
      dump_const_value_smt (sdc, "1", BTOR_OUTPUT_BASE_BIN);
      fputc (' ', sdc->file);
      DUMP_EXP_SMT (real_exp->e[0]);
      fputs (") ", sdc->file);
      DUMP_EXP_SMT (real_exp->e[1]);
      fputc (' ', sdc->file);
      DUMP_EXP_SMT (real_exp->e[2]);
      fputc (')', sdc->file);
      break;

    case BTOR_FEQ_NODE:
    case BTOR_BEQ_NODE:
    case BTOR_ULT_NODE:
      fputc ('(', sdc->file);
      /* do not wrap boolean nodes if they are roots */
      if (!is_root (sdc, exp)) fputs ("ite (", sdc->file);
      if (real_exp->kind == BTOR_ULT_NODE)
        fputs ("bvult", sdc->file);
      else
        fputc ('=', sdc->file);
      fputc (' ', sdc->file);
      DUMP_EXP_SMT (real_exp->e[0]);
      fputc (' ', sdc->file);
      DUMP_EXP_SMT (real_exp->e[1]);
      fputc (')', sdc->file);
      /* do not wrap boolean nodes if they are roots */
      if (!is_root (sdc, exp))
      {
        fputc (' ', sdc->file);
        dump_const_value_smt (sdc, "1", BTOR_OUTPUT_BASE_BIN);
        fputc (' ', sdc->file);
        dump_const_value_smt (sdc, "0", BTOR_OUTPUT_BASE_BIN);
        fputc (')', sdc->file);
      }
      break;

    case BTOR_APPLY_NODE:
      fputc ('(', sdc->file);
      /* array select */
      if (BTOR_IS_UF_ARRAY_NODE (real_exp->e[0]))
      {
        fputs ("select ", sdc->file);
        DUMP_EXP_SMT (real_exp->e[0]);
        fputc (' ', sdc->file);
        assert (BTOR_IS_REGULAR_NODE (real_exp->e[1]));
        assert (((BtorArgsNode *) real_exp->e[1])->num_args == 1);
        DUMP_EXP_SMT (real_exp->e[1]->e[0]);
      }
      /* function application */
      else
      {
        DUMP_EXP_SMT (real_exp->e[0]);

        init_args_iterator (&it, real_exp->e[1]);
        while (has_next_args_iterator (&it))
        {
          arg = next_args_iterator (&it);
          fputc (' ', sdc->file);
          DUMP_EXP_SMT (arg);
        }
      }
      fputc (')', sdc->file);
      break;

#if 0
      case BTOR_LAMBDA_NODE:
	extract_store (sdc, exp, &index, &value, &array);
	assert (index);
	assert (value);
	assert (array);
	fputs ("(store ", sdc->file);
	DUMP_EXP_SMT (array);
	fputc (' ', sdc->file);
	DUMP_EXP_SMT (index);
	fputc (' ', sdc->file);
	DUMP_EXP_SMT (value);
	fputc (')', sdc->file);
	break;
#endif

    default:
      fputc ('(', sdc->file);

      switch (real_exp->kind)
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

      for (i = 0; i < real_exp->arity; i++)
      {
        fputc (' ', sdc->file);
        DUMP_EXP_SMT (real_exp->e[i]);
      }

      fputc (')', sdc->file);
  }

  /* close bvnot for non-constants */
  if (BTOR_IS_INVERTED_NODE (exp) && !BTOR_IS_BV_CONST_NODE (real_exp))
    fputc (')', sdc->file);

  /* always dump constans and function applications */
  if (!BTOR_IS_BV_CONST_NODE (real_exp) && !BTOR_IS_APPLY_NODE (real_exp))
    btor_insert_in_ptr_hash_table (sdc->mark, real_exp);
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
    recursively_dump_exp_smt (sdc, exp, 0, -1);
    fputs (")\n", sdc->file);
  }
  else
  {
    fputs ("(let ((", sdc->file);
    dump_smt_id (sdc, exp);
    fputc (' ', sdc->file);
    recursively_dump_exp_smt (sdc, exp, 0, -1);
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
  btor_dump_sort_smt_node (exp, sdc->version, sdc->file);
  fputc (' ', sdc->file);
  recursively_dump_exp_smt (sdc, exp, 0, -1);
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

  int i, refs;
  BtorNode *cur, *param, *index = 0, *value = 0, *array = 0;
  BtorMemMgr *mm = sdc->btor->mm;
  BtorNodePtrStack visit, shared;
  BtorNodeIterator it;
  BtorPtrHashTable *mark;
  BtorPtrHashBucket *b;

  mark = btor_new_ptr_hash_table (mm,
                                  (BtorHashPtr) btor_hash_exp_by_id,
                                  (BtorCmpPtr) btor_compare_exp_by_id);
  BTOR_INIT_STACK (visit);
  BTOR_INIT_STACK (shared);

#if 0
  extract_store (sdc, fun, &index, &value, &array);

  if (index)
    {
      assert (value);
      assert (array);
      btor_insert_in_ptr_hash_table (sdc->stores, fun);
      return;
    }
#endif

  /* collect shared parameterized expressions in function body */
  BTOR_PUSH_STACK (mm, visit, BTOR_REAL_ADDR_NODE (BTOR_LAMBDA_GET_BODY (fun)));
  while (!BTOR_EMPTY_STACK (visit))
  {
    cur = BTOR_POP_STACK (visit);
    assert (BTOR_IS_REGULAR_NODE (cur));
    b = btor_find_in_ptr_hash_table (sdc->dump, cur);
    assert (b);
    refs = b->data.asInt;

    if (btor_find_in_ptr_hash_table (mark, cur)
        || BTOR_IS_FUN_NODE (cur)
        /* skip non-parameterized expressions shared in the formula */
        || !cur->parameterized && refs > 1)
      continue;

    /* args and params are handled differently */
    /* collect shared parameterized expressions in function body.
     * arguments, parameters, and constants are excluded. */
    if (!BTOR_IS_ARGS_NODE (cur)
        && !BTOR_IS_PARAM_NODE (cur)
        /* constants are always printed */
        && !BTOR_IS_BV_CONST_NODE (cur) && cur->parameterized && refs > 1)
      BTOR_PUSH_STACK (mm, shared, cur);

    btor_insert_in_ptr_hash_table (mark, cur);
    for (i = 0; i < cur->arity; i++)
      BTOR_PUSH_STACK (mm, visit, BTOR_REAL_ADDR_NODE (cur->e[i]));
  }

  /* dump function signature */
  fputs ("(define-fun ", sdc->file);
  dump_smt_id (sdc, fun);
  fputs (" (", sdc->file);

  // TODO (ma): add space between parameters
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
    btor_dump_sort_smt_node (param, sdc->version, sdc->file);
    fputc (')', sdc->file);
  }
  fputs (") ", sdc->file);

  btor_dump_sort_smt_node (fun, sdc->version, sdc->file);
  fputc (' ', sdc->file);

  assert (sdc->open_lets == 0);

  /* dump expressions that are shared in 'fun' */
  if (shared.start)
    qsort (shared.start,
           BTOR_COUNT_STACK (shared),
           sizeof (BtorNode *),
           cmp_node_id);

  while (!BTOR_EMPTY_STACK (shared))
  {
    cur = BTOR_POP_STACK (shared);
    assert (BTOR_IS_REGULAR_NODE (cur));
    assert (cur->parameterized);
    dump_let_smt (sdc, cur);
    fputc (' ', sdc->file);
  }
  recursively_dump_exp_smt (sdc, BTOR_LAMBDA_GET_BODY (fun), 0, -1);

  /* close lets */
  for (i = 0; i < sdc->open_lets; i++) fputc (')', sdc->file);
  sdc->open_lets = 0;

  /* close define-fun */
  fputs (")\n", sdc->file);

  BTOR_RELEASE_STACK (mm, shared);
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
    btor_dump_sort_smt_node (exp, sdc->version, sdc->file);
    fputs ("))\n", sdc->file);
  }
  else
  {
    fputs ("(declare-fun ", sdc->file);
    dump_smt_id (sdc, exp);
    fputc (' ', sdc->file);
    if (BTOR_IS_BV_VAR_NODE (exp) || BTOR_IS_UF_ARRAY_NODE (exp))
      fputs ("() ", sdc->file);
    btor_dump_sort_smt_node (exp, sdc->version, sdc->file);
    fputs (")\n", sdc->file);
  }
  btor_insert_in_ptr_hash_table (sdc->mark, exp);
}

static int
is_bool (BtorSMTDumpContext *sdc, BtorNode *exp)
{
  return BTOR_IS_BV_EQ_NODE (BTOR_REAL_ADDR_NODE (exp))
         || BTOR_IS_ULT_NODE (BTOR_REAL_ADDR_NODE (exp))
         || BTOR_IS_FUN_EQ_NODE (BTOR_REAL_ADDR_NODE (exp))
         || BTOR_REAL_ADDR_NODE (exp)
                == BTOR_REAL_ADDR_NODE (sdc->btor->true_exp);
}

static void
dump_assert_smt2 (BtorSMTDumpContext *sdc, BtorNode *exp)
{
  assert (sdc);
  assert (sdc->version == 2);
  assert (exp);
  assert (BTOR_REAL_ADDR_NODE (exp)->len == 1);

  fputs ("(assert ", sdc->file);
  if (!is_bool (sdc, exp)) fputs ("(distinct ", sdc->file);
  if (exp == sdc->btor->true_exp)
    fputs ("true", sdc->file);
  else if (exp == BTOR_INVERT_NODE (sdc->btor->true_exp))
    fputs ("false", sdc->file);
  else
    recursively_dump_exp_smt (sdc, exp, 0, -1);
  if (!is_bool (sdc, exp)) fputs (" #b0)", sdc->file);
  fputs (")\n", sdc->file);
}

static void
set_logic_smt (BtorSMTDumpContext *sdc, const char *logic)
{
  assert (sdc);

  const char *fmt;

  fmt = sdc->version == 1 ? ":logic %s\n" : "(set-logic %s)\n";
  fprintf (sdc->file, fmt, logic);
}

static void
wrap_non_bool_root_smt1 (BtorSMTDumpContext *sdc, BtorNode *exp)
{
  assert (sdc->version == 1);
  if (!is_bool (sdc, exp)) fputs ("(not (= ", sdc->file);
  if (exp == sdc->btor->true_exp)
    fputs ("true", sdc->file);
  else if (exp == BTOR_INVERT_NODE (sdc->btor->true_exp))
    fputs ("false", sdc->file);
  else
    dump_smt_id (sdc, exp);
  if (!is_bool (sdc, exp))
    fprintf (sdc->file, " bv0[%d]))", BTOR_REAL_ADDR_NODE (exp)->len);
}

static int
get_references (BtorSMTDumpContext *sdc, BtorNode *exp)
{
  assert (exp);

  int refs = 0;
  BtorNode *cur;
  BtorNodeIterator it;
  BtorPtrHashBucket *b;

  exp = BTOR_REAL_ADDR_NODE (exp);

  /* get reference count of roots */
  if (btor_find_in_ptr_hash_table (sdc->roots, exp)) refs++;
  if (btor_find_in_ptr_hash_table (sdc->roots, BTOR_INVERT_NODE (exp))) refs++;

  init_full_parent_iterator (&it, exp);
  while (has_next_parent_full_parent_iterator (&it))
  {
    cur = next_parent_full_parent_iterator (&it);
    assert (BTOR_IS_REGULAR_NODE (cur));
    b = btor_find_in_ptr_hash_table (sdc->dump, cur);
    if (!b) continue;

    if (BTOR_IS_ARGS_NODE (exp))
      refs += b->data.asInt;
    else if (BTOR_IS_ARGS_NODE (cur))
      refs += b->data.asInt;
    else
      refs++;
  }
  return refs;
}

static void
dump_smt (BtorSMTDumpContext *sdc)
{
  assert (sdc);

  int i, j;
  BtorNode *e, *cur, *real_cur;  // *cur_parent;
  BtorMemMgr *mm;
  BtorNodePtrStack visit, all, vars, arrays, shared, ufs;
  BtorPtrHashBucket *b;
  BtorHashTableIterator it;

  mm = sdc->btor->mm;
  BTOR_INIT_STACK (visit);
  BTOR_INIT_STACK (shared);
  BTOR_INIT_STACK (all);
  BTOR_INIT_STACK (vars);
  BTOR_INIT_STACK (arrays);
  BTOR_INIT_STACK (ufs);

  init_node_hash_table_iterator (&it, sdc->roots);
  while (has_next_node_hash_table_iterator (&it))
  {
    cur      = next_node_hash_table_iterator (&it);
    real_cur = BTOR_REAL_ADDR_NODE (cur);
    assert (!btor_find_in_ptr_hash_table (sdc->mark, real_cur));
    BTOR_PUSH_STACK (mm, visit, real_cur);
    //      BTOR_PUSH_STACK (mm, visit, 0);
  }

  /* collect constants, variables, array variables and functions */
  while (!BTOR_EMPTY_STACK (visit))
  {
    //      cur_parent = BTOR_POP_STACK (visit);
    cur = BTOR_POP_STACK (visit);
    assert (BTOR_IS_REGULAR_NODE (cur));

    if (btor_find_in_ptr_hash_table (sdc->dump, cur)) continue;

#if 0
      /* extract boolean top layer */
      if (!cur_parent
	  || (btor_find_in_ptr_hash_table (sdc->boolean, cur_parent)
	      && cur->len == 1
	      && (BTOR_IS_BV_CONST_NODE (cur)
		  || BTOR_IS_BV_VAR_NODE (cur)
		  || BTOR_IS_AND_NODE (cur)
		  || BTOR_IS_BV_EQ_NODE (cur)
		  || BTOR_IS_ULT_NODE (cur))))
	{
	  BTOR_PUSH_STACK (mm, boolean, cur);
	  btor_insert_in_ptr_hash_table (sdc->boolean, cur);
	}
#endif

    btor_insert_in_ptr_hash_table (sdc->dump, cur);
    if (sdc->version == 1)
    {
      if (!BTOR_IS_ARGS_NODE (cur) && !BTOR_IS_BV_CONST_NODE (cur))
        BTOR_PUSH_STACK (mm, shared, cur);
    }
    else
      BTOR_PUSH_STACK (mm, all, cur);

    if (BTOR_IS_BV_VAR_NODE (cur))
      BTOR_PUSH_STACK (mm, vars, cur);
    else if (BTOR_IS_UF_ARRAY_NODE (cur))
      BTOR_PUSH_STACK (mm, arrays, cur);
    else if (BTOR_IS_UF_NODE (cur))
      BTOR_PUSH_STACK (mm, ufs, cur);
    else if (BTOR_IS_LAMBDA_NODE (cur) && !cur->parameterized
             && (!BTOR_IS_CURRIED_LAMBDA_NODE (cur)
                 || BTOR_IS_FIRST_CURRIED_LAMBDA (cur)))
      BTOR_PUSH_STACK (mm, shared, cur);

    for (j = 0; j < cur->arity; j++)
    {
      BTOR_PUSH_STACK (mm, visit, BTOR_REAL_ADDR_NODE (cur->e[j]));
      //	  BTOR_PUSH_STACK (mm, visit, cur);
    }
  }

  /* collect nodes that are referenced more than once
   * (inputs, constants, functions, and function applications excluded) */
  if (sdc->version == 2)
  {
    if (all.start)
      qsort (all.start, BTOR_COUNT_STACK (all), sizeof e, cmp_node_id);

    for (i = BTOR_COUNT_STACK (all) - 1; i >= 0; i--)
    {
      cur = BTOR_PEEK_STACK (all, i);
      b   = btor_find_in_ptr_hash_table (sdc->dump, cur);
      /* cache result for later reuse */
      b->data.asInt = get_references (sdc, cur);

      if (b->data.asInt <= 1 || cur->parameterized
          || BTOR_IS_BV_CONST_NODE (cur) || BTOR_IS_BV_VAR_NODE (cur)
          || BTOR_IS_APPLY_NODE (cur) || BTOR_IS_FUN_NODE (cur)
          || BTOR_IS_PARAM_NODE (cur) || BTOR_IS_ARGS_NODE (cur))
        continue;

      BTOR_PUSH_STACK (mm, shared, cur);
    }
  }

  /* begin dump */
  if (sdc->version == 1) fputs ("(benchmark dump\n", sdc->file);

  if (BTOR_EMPTY_STACK (arrays) && BTOR_EMPTY_STACK (ufs))
    set_logic_smt (sdc, "QF_BV");
  else if (BTOR_EMPTY_STACK (arrays))
    set_logic_smt (sdc, "QF_UFBV");
  else if (BTOR_EMPTY_STACK (ufs))
    set_logic_smt (sdc, "QF_ABV");
  else
    set_logic_smt (sdc, "QF_AUFBV");

  /* dump inputs */
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

  /* dump shared expressions and functions */
  if (shared.start)
    qsort (shared.start, BTOR_COUNT_STACK (shared), sizeof e, cmp_node_id);

  for (i = 0; i < BTOR_COUNT_STACK (shared); i++)
  {
    cur = BTOR_PEEK_STACK (shared, i);
    assert (BTOR_IS_REGULAR_NODE (cur));

    if (btor_find_in_ptr_hash_table (sdc->mark, cur)) continue;

    assert (!cur->parameterized);

    if (sdc->version == 1)
    {
      assert (!BTOR_IS_LAMBDA_NODE (cur));
      dump_let_smt (sdc, cur);
    }
    else
    {
      if (BTOR_IS_LAMBDA_NODE (cur))
        dump_fun_smt2 (sdc, cur);
      else
        dump_fun_let_smt2 (sdc, cur);
    }
  }

  /* dump assertions/build root */
  if (sdc->version == 1)
  {
    i = 0;
    init_node_hash_table_iterator (&it, sdc->roots);
    while (has_next_node_hash_table_iterator (&it))
    {
      cur = next_node_hash_table_iterator (&it);
      if (i < (int) sdc->roots->count - 1) fputs (" (and", sdc->file);
      fputc (' ', sdc->file);
      wrap_non_bool_root_smt1 (sdc, cur);
      i++;
    }

    for (i = 0; i < (int) sdc->roots->count + sdc->open_lets; i++)
      fputc (')', sdc->file);

    fputc ('\n', sdc->file);
    sdc->open_lets = 0;
  }
  else
  {
    init_node_hash_table_iterator (&it, sdc->roots);
    while (has_next_node_hash_table_iterator (&it))
    {
      cur = next_node_hash_table_iterator (&it);
      dump_assert_smt2 (sdc, cur);
    }
  }
  assert (sdc->open_lets == 0);

#ifndef NDEBUG
  init_node_hash_table_iterator (&it, sdc->dump);
  while (has_next_node_hash_table_iterator (&it))
  {
    cur = next_node_hash_table_iterator (&it);
    /* constants and function applications are always dumped (hence, not in
     * mark) */
    if (BTOR_IS_BV_CONST_NODE (cur)
        || BTOR_IS_APPLY_NODE (cur)
        /* argument nodes are never dumped and not in mark */
        || BTOR_IS_ARGS_NODE (cur))
      continue;
    assert (btor_find_in_ptr_hash_table (sdc->mark, cur));
  }
#endif

  BTOR_RELEASE_STACK (mm, shared);
  BTOR_RELEASE_STACK (mm, visit);
  BTOR_RELEASE_STACK (mm, all);
  BTOR_RELEASE_STACK (mm, vars);
  BTOR_RELEASE_STACK (mm, arrays);
  BTOR_RELEASE_STACK (mm, ufs);

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

#ifndef NDEBUG
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
    temp = next_node_hash_table_iterator (&it);

    if (temp->parameterized && !BTOR_IS_CURRIED_LAMBDA_NODE (temp))
    {
      nested_funs = 1;
      break;
    }
  }

  for (i = 0; i < nroots; i++) tmp_roots[i] = roots[i];

  if (nested_funs || version == 1)
  {
#ifndef NDEBUG
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

#ifndef NDEBUG
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
