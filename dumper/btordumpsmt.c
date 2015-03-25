/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2013 Armin Biere.
 *  Copyright (C) 2012-2015 Mathias Preiner.
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
  BtorPtrHashTable *dumped;
  BtorPtrHashTable *boolean;
  BtorPtrHashTable *stores;
  BtorPtrHashTable *idtab;
  BtorPtrHashTable *roots;
  BtorPtrHashTable *const_cache;
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

  sdc->btor        = btor;
  sdc->dump        = btor_new_ptr_hash_table (btor->mm,
                                       (BtorHashPtr) btor_hash_exp_by_id,
                                       (BtorCmpPtr) btor_compare_exp_by_id);
  sdc->dumped      = btor_new_ptr_hash_table (btor->mm,
                                         (BtorHashPtr) btor_hash_exp_by_id,
                                         (BtorCmpPtr) btor_compare_exp_by_id);
  sdc->boolean     = btor_new_ptr_hash_table (btor->mm,
                                          (BtorHashPtr) btor_hash_exp_by_id,
                                          (BtorCmpPtr) btor_compare_exp_by_id);
  sdc->stores      = btor_new_ptr_hash_table (btor->mm,
                                         (BtorHashPtr) btor_hash_exp_by_id,
                                         (BtorCmpPtr) btor_compare_exp_by_id);
  sdc->idtab       = btor_new_ptr_hash_table (btor->mm,
                                        (BtorHashPtr) btor_hash_exp_by_id,
                                        (BtorCmpPtr) btor_compare_exp_by_id);
  sdc->const_cache = btor_new_ptr_hash_table (
      btor->mm, (BtorHashPtr) btor_hash_str, (BtorCmpPtr) strcmp);
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
  btor_delete_ptr_hash_table (sdc->dumped);
  btor_delete_ptr_hash_table (sdc->boolean);
  btor_delete_ptr_hash_table (sdc->stores);
  btor_delete_ptr_hash_table (sdc->idtab);

  init_node_hash_table_iterator (&it, sdc->roots);
  while (has_next_node_hash_table_iterator (&it))
    btor_release_exp (sdc->btor, next_node_hash_table_iterator (&it));
  btor_delete_ptr_hash_table (sdc->roots);

  init_hash_table_iterator (&it, sdc->const_cache);
  while (has_next_hash_table_iterator (&it))
  {
    assert (it.bucket->data.asStr);
    btor_freestr (sdc->btor->mm, it.bucket->data.asStr);
    btor_freestr (sdc->btor->mm, (char *) next_hash_table_iterator (&it));
  }
  btor_delete_ptr_hash_table (sdc->const_cache);
  BTOR_DELETE (sdc->btor->mm, sdc);
}

static void
add_root_to_smt_dump_context (BtorSMTDumpContext *sdc, BtorNode *root)
{
  if (!btor_find_in_ptr_hash_table (sdc->roots, root))
    btor_insert_in_ptr_hash_table (sdc->roots, btor_copy_exp (sdc->btor, root));
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
  if (BTOR_IS_BV_VAR_NODE (exp) && ((BtorBVVarNode *) exp)->btor_id)
    return ((BtorBVVarNode *) exp)->btor_id;
  if ((BTOR_IS_UF_ARRAY_NODE (exp) || BTOR_IS_UF_NODE (exp))
      && ((BtorUFNode *) exp)->btor_id)
    return ((BtorUFNode *) exp)->btor_id;
  return exp->id;
}

static void
dump_smt_id (BtorSMTDumpContext *sdc, BtorNode *exp)
{
  assert (sdc);
  assert (exp);

  const char *type, *sym;

  exp = BTOR_REAL_ADDR_NODE (exp);

  switch (exp->kind)
  {
    case BTOR_BV_VAR_NODE: type = "v"; goto DUMP_SYMBOL;

    case BTOR_PARAM_NODE:
      type = "p";
    DUMP_SYMBOL:
      sym = btor_get_symbol_exp (sdc->btor, exp);
      if (sym && !isdigit (sym[0]))
      {
        fputs (sym, sdc->file);
        return;
      }
      break;

    case BTOR_UF_NODE:
      type = BTOR_IS_UF_ARRAY_NODE (exp) ? "a" : "uf";
      goto DUMP_SYMBOL;

    case BTOR_LAMBDA_NODE: type = "f"; goto DUMP_SYMBOL;

    default: type = sdc->version == 1 ? "?e" : "$e";
  }

  fprintf (sdc->file, "%s%d", type, smt_id (sdc, exp));
}

static int
is_boolean (BtorSMTDumpContext *sdc, BtorNode *exp)
{
  exp = BTOR_REAL_ADDR_NODE (exp);
  return btor_find_in_ptr_hash_table (sdc->boolean, exp) != 0;
}

void
btor_dump_const_value_smt (
    Btor *btor, const char *bits, int base, int version, FILE *file)
{
  assert (btor);
  assert (bits);
  assert (base == BTOR_OUTPUT_BASE_BIN || base == BTOR_OUTPUT_BASE_DEC
          || base == BTOR_OUTPUT_BASE_HEX);

  char *val;
  const char *fmt;

  /* SMT-LIB v1.2 only supports decimal output */
  if (base == BTOR_OUTPUT_BASE_DEC || version == 1)
  {
    val = btor_const_to_decimal (btor->mm, bits);
    fmt = version == 1 ? "bv%s[%d]" : "(_ bv%s %d)";
    fprintf (file, fmt, val, strlen (bits));
    btor_freestr (btor->mm, val);
  }
  else if (base == BTOR_OUTPUT_BASE_HEX && strlen (bits) % 4 == 0)
  {
    assert (version == 2);
    val = btor_const_to_hex (btor->mm, bits);
    fprintf (file, "#x%s", val);
    btor_freestr (btor->mm, val);
  }
  else
  {
    assert (version == 2);
    fprintf (file, "#b%s", bits);
  }
}

static void
dump_const_value_aux_smt (BtorSMTDumpContext *sdc, const char *bits)
{
  assert (sdc);
  assert (bits);

  int base, version;
  FILE *file;
  char *val;
  const char *fmt;
  BtorPtrHashBucket *b;

  base    = sdc->btor->options.output_number_format.val;
  version = sdc->version;
  file    = sdc->file;

  /* converting consts to decimal/hex is costly. we now always dump the value of
   * constants. in order to avoid computing the same value again we cache
   * the result of the first computation and print the cached value in
   * subsequent calls. */
  if (base == BTOR_OUTPUT_BASE_DEC || version == 1)
  {
    if ((b = btor_find_in_ptr_hash_table (sdc->const_cache, (char *) bits)))
    {
      val = b->data.asStr;
      assert (val);
    }
    else
    {
      val = btor_const_to_decimal (sdc->btor->mm, bits);
      btor_insert_in_ptr_hash_table (sdc->const_cache,
                                     btor_strdup (sdc->btor->mm, bits))
          ->data.asStr = val;
    }
    fmt = version == 1 ? "bv%s[%d]" : "(_ bv%s %d)";
    fprintf (file, fmt, val, strlen (bits));
  }
  else if (base == BTOR_OUTPUT_BASE_HEX && strlen (bits) % 4 == 0)
  {
    assert (version == 2);
    if ((b = btor_find_in_ptr_hash_table (sdc->const_cache, (char *) bits)))
    {
      val = b->data.asStr;
      assert (val);
    }
    else
    {
      val = btor_const_to_hex (sdc->btor->mm, bits);
      btor_insert_in_ptr_hash_table (sdc->const_cache,
                                     btor_strdup (sdc->btor->mm, bits))
          ->data.asStr = val;
    }
    fprintf (file, "#x%s", val);
  }
  else
    btor_dump_const_value_smt (sdc->btor, bits, base, version, file);
}

void
btor_dump_sort_smt (BtorSort *sort, int version, FILE *file)
{
  unsigned i;
  const char *fmt;

  switch (sort->kind)
  {
    case BTOR_BOOL_SORT: fputs ("Bool", file); break;

    case BTOR_BITVEC_SORT:
      fmt = version == 1 ? "BitVec[%d]" : "(_ BitVec %d)";
      fprintf (file, fmt, sort->bitvec.width);
      break;

    case BTOR_ARRAY_SORT:
      fmt =
          version == 1 ? "Array[%d:%d]" : "(Array (_ BitVec %d) (_ BitVec %d))";
      assert (sort->array.index->kind == BTOR_BITVEC_SORT);
      assert (sort->array.element->kind == BTOR_BITVEC_SORT);
      fprintf (file,
               fmt,
               sort->array.index->bitvec.width,
               sort->array.element->bitvec.width);
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

  BtorSort *sort;

  exp  = BTOR_REAL_ADDR_NODE (exp);
  sort = btor_get_sort_by_id (&exp->btor->sorts_unique_table, exp->sort_id);
  btor_dump_sort_smt (sort, version, file);
}

#if 0
static void
extract_store (BtorSMTDumpContext * sdc, BtorNode * exp,
	       BtorNode ** index, BtorNode ** value, BtorNode ** array)
{
  BtorNode *ite, *eq, *apply;

  if (!BTOR_IS_LAMBDA_NODE (exp))
    return;

  if (((BtorLambdaNode *) exp)->num_params != 1)
    return;

  if (!BTOR_IS_BV_COND_NODE (BTOR_REAL_ADDR_NODE (exp->e[1])))
    return;

  ite = exp->e[1];
  if (BTOR_IS_INVERTED_NODE (ite))
    return;

  if (!BTOR_IS_BV_EQ_NODE (BTOR_REAL_ADDR_NODE (ite->e[0])))
    return;

  /* check ite condition */
  eq = ite->e[0];
  if (BTOR_IS_INVERTED_NODE (eq))
    return;

  if (!eq->parameterized)
    return;

  /* check if branch */
  if (BTOR_REAL_ADDR_NODE (ite->e[1])->parameterized)
    return;

  /* check else branch */
  if (!BTOR_REAL_ADDR_NODE (ite->e[2])->parameterized)
    return;

  if (!BTOR_IS_APPLY_NODE (BTOR_REAL_ADDR_NODE (ite->e[2])))
    return;

  apply = ite->e[2];
  if (BTOR_IS_INVERTED_NODE (apply))
    return;

  if (!BTOR_IS_UF_ARRAY_NODE (apply->e[0])
      && !btor_find_in_ptr_hash_table (sdc->stores, apply->e[0]))
    return;

  if (!BTOR_IS_PARAM_NODE (BTOR_REAL_ADDR_NODE (apply->e[1]->e[0])))
    return;

  *index = BTOR_REAL_ADDR_NODE (eq->e[0])->parameterized ? eq->e[1] : eq->e[0];
  *value = ite->e[1];
  *array = apply->e[0];
}
#endif

#define PUSH_DUMP_NODE(exp, expect_bv, expect_bool, add_space, zero_ext) \
  {                                                                      \
    BTOR_PUSH_STACK (mm, dump, exp);                                     \
    BTOR_PUSH_STACK (mm, expect_bv_stack, expect_bv);                    \
    BTOR_PUSH_STACK (mm, expect_bool_stack, expect_bool);                \
    BTOR_PUSH_STACK (mm, add_space_stack, add_space);                    \
    BTOR_PUSH_STACK (mm, zero_extend_stack, zero_ext);                   \
  }

// TODO (ma): implement depth_limit
static void
recursively_dump_exp_smt (BtorSMTDumpContext *sdc, BtorNode *exp, int expect_bv)
{
  assert (sdc);
  assert (exp);
  assert (btor_find_in_ptr_hash_table (sdc->dump, BTOR_REAL_ADDR_NODE (exp)));

  int pad, i, is_bool, add_space, zero_extend, expect_bool;
  char *inv_bits;
  const char *op, *fmt;
  BtorNode *arg, *real_exp;
  BtorArgsIterator it;
  BtorNodePtrStack dump, args;
  BtorIntStack expect_bv_stack, expect_bool_stack;
  BtorIntStack add_space_stack, zero_extend_stack;
  BtorPtrHashTable *visited;
  BtorMemMgr *mm;

  mm      = sdc->btor->mm;
  visited = btor_new_ptr_hash_table (mm, 0, 0);
  BTOR_INIT_STACK (args);
  BTOR_INIT_STACK (dump);
  BTOR_INIT_STACK (expect_bv_stack);
  BTOR_INIT_STACK (expect_bool_stack);
  BTOR_INIT_STACK (add_space_stack);
  BTOR_INIT_STACK (zero_extend_stack);

  PUSH_DUMP_NODE (exp, expect_bv, 0, 0, 0);
  while (!BTOR_EMPTY_STACK (dump))
  {
    assert (!BTOR_EMPTY_STACK (expect_bv_stack));
    assert (!BTOR_EMPTY_STACK (expect_bool_stack));
    assert (!BTOR_EMPTY_STACK (add_space_stack));
    assert (!BTOR_EMPTY_STACK (zero_extend_stack));
    exp         = BTOR_POP_STACK (dump);
    expect_bv   = BTOR_POP_STACK (expect_bv_stack);
    expect_bool = BTOR_POP_STACK (expect_bool_stack);
    add_space   = BTOR_POP_STACK (add_space_stack);
    zero_extend = BTOR_POP_STACK (zero_extend_stack);
    real_exp    = BTOR_REAL_ADDR_NODE (exp);
    is_bool     = is_boolean (sdc, real_exp);
    assert (!expect_bv || !expect_bool);
    assert (!expect_bool || !expect_bv);

    /* open s-expression */
    if (!btor_find_in_ptr_hash_table (visited, real_exp))
    {
      if (add_space) fputc (' ', sdc->file);

      /* wrap node with zero_extend */
      if (zero_extend)
      {
        fmt =
            sdc->version == 1 ? " (zero_extend[%d] " : " ((_ zero_extend %d) ";
        fprintf (sdc->file, fmt, pad);
      }

      /* always print constants */
      if (BTOR_IS_BV_CONST_NODE (real_exp))
      {
        if (exp == sdc->btor->true_exp && !expect_bv)
          fputs ("true", sdc->file);
        else if (exp == BTOR_INVERT_NODE (sdc->btor->true_exp) && !expect_bv)
          fputs ("false", sdc->file);
        else if (BTOR_IS_INVERTED_NODE (exp))
        {
          inv_bits = btor_not_const (sdc->btor->mm, real_exp->bits);
          dump_const_value_aux_smt (sdc, inv_bits);
          btor_freestr (sdc->btor->mm, inv_bits);
        }
        else
          dump_const_value_aux_smt (sdc, real_exp->bits);

        /* close zero extend */
        if (zero_extend) fputc (')', sdc->file);
        continue;
      }

      /* wrap non-bool node and make it bool */
      if (expect_bool && !is_bool)
      {
        fputs ("(= ", sdc->file);
        dump_const_value_aux_smt (sdc, "1");
        fputc (' ', sdc->file);
      }

      /* wrap node with bvnot/not */
      if (BTOR_IS_INVERTED_NODE (exp))
        fputs (expect_bv || !is_bool ? "(bvnot " : "(not ", sdc->file);

      /* wrap bool node and make it a bit vector expression */
      if (is_bool && expect_bv) fputs ("(ite ", sdc->file);

      if (btor_find_in_ptr_hash_table (sdc->dumped, real_exp)
          || BTOR_IS_FUN_NODE (real_exp))
      {
#ifndef NDEBUG
        BtorPtrHashBucket *b;
        b = btor_find_in_ptr_hash_table (sdc->dump, real_exp);
        assert (b);
        /* functions and variables are declared separately */
        assert (BTOR_IS_FUN_NODE (real_exp) || BTOR_IS_BV_VAR_NODE (real_exp)
                || b->data.asInt > 1);
#endif
        dump_smt_id (sdc, exp);
        goto CLOSE_WRAPPER;
      }

      PUSH_DUMP_NODE (exp, expect_bv, expect_bool, 0, zero_extend);
      btor_insert_in_ptr_hash_table (visited, real_exp);
      op = "";
      switch (real_exp->kind)
      {
        case BTOR_SLL_NODE:
        case BTOR_SRL_NODE:
          assert (!is_bool);
          op = real_exp->kind == BTOR_SRL_NODE ? "bvlshr" : "bvshl";
          assert (btor_get_exp_width (sdc->btor, real_exp) > 1);
          pad = btor_get_exp_width (sdc->btor, real_exp)
                - btor_get_exp_width (sdc->btor, real_exp->e[1]);
          PUSH_DUMP_NODE (real_exp->e[1], 1, 0, 1, pad);
          PUSH_DUMP_NODE (real_exp->e[0], 1, 0, 1, 0);
          break;

        case BTOR_BCOND_NODE:
          op = "ite";
          PUSH_DUMP_NODE (real_exp->e[2], !is_bool, 0, 1, 0);
          PUSH_DUMP_NODE (real_exp->e[1], !is_bool, 0, 1, 0);
          PUSH_DUMP_NODE (real_exp->e[0], 0, 1, 1, 0);
          break;

        case BTOR_APPLY_NODE:
          /* array select */
          if (BTOR_IS_UF_ARRAY_NODE (real_exp->e[0])) op = "select ";

          /* we need the arguments in reversed order */
          init_args_iterator (&it, real_exp->e[1]);
          while (has_next_args_iterator (&it))
          {
            arg = next_args_iterator (&it);
            BTOR_PUSH_STACK (mm, args, arg);
          }
          while (!BTOR_EMPTY_STACK (args))
          {
            arg = BTOR_POP_STACK (args);
            // TODO (ma): what about bool arguments/indices
            PUSH_DUMP_NODE (arg, 1, 0, 1, 0);
          }
          PUSH_DUMP_NODE (real_exp->e[0], 1, 0, 0, 0);
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
          expect_bv = 1;
          switch (real_exp->kind)
          {
            case BTOR_FEQ_NODE:
            case BTOR_BEQ_NODE:
              op        = "=";
              expect_bv = 1;
              break;
            case BTOR_ULT_NODE:
              op        = "bvult";
              expect_bv = 1;
              break;
            case BTOR_SLICE_NODE:
              assert (!is_bool);
              op = sdc->version == 1 ? "extract" : "(_ extract ";
              break;
            case BTOR_AND_NODE:
              op        = is_bool ? "and" : "bvand";
              expect_bv = !is_bool;
              break;
            case BTOR_ADD_NODE:
              assert (!is_bool);
              op = "bvadd";
              break;
            case BTOR_MUL_NODE:
              assert (!is_bool);
              op = "bvmul";
              break;
            case BTOR_UDIV_NODE:
              assert (!is_bool);
              op = "bvudiv";
              break;
            case BTOR_UREM_NODE:
              assert (!is_bool);
              op = "bvurem";
              break;
            case BTOR_CONCAT_NODE:
              assert (!is_bool);
              op = "concat";
              break;
            default: assert (0); op = "unknown";
          }
          for (i = real_exp->arity - 1; i >= 0; i--)
            PUSH_DUMP_NODE (real_exp->e[i], expect_bv, 0, 1, 0);
      }

      /* open s-expression */
      assert (op);
      fprintf (sdc->file, "(%s", op);

      if (BTOR_IS_SLICE_NODE (real_exp))
      {
        fmt = sdc->version == 1 ? "[%d:%d]" : "%d %d)";
        fprintf (sdc->file, fmt, real_exp->upper, real_exp->lower);
      }
    }
    /* close s-expression */
    else
    {
      if (!btor_find_in_ptr_hash_table (sdc->dumped, real_exp))
        btor_insert_in_ptr_hash_table (sdc->dumped, real_exp);

      /* close s-expression */
      if (real_exp->arity > 0) fputc (')', sdc->file);

    CLOSE_WRAPPER:
      /* close wrappers */

      /* wrap boolean expressions in bit vector expression */
      if (is_bool && expect_bv && !BTOR_IS_BV_CONST_NODE (real_exp))
      {
        fputc (' ', sdc->file);
        dump_const_value_aux_smt (sdc, "1");
        fputc (' ', sdc->file);
        dump_const_value_aux_smt (sdc, "0");
        fputc (')', sdc->file);
      }

      /* close bvnot for non-constants */
      if (BTOR_IS_INVERTED_NODE (exp) && !BTOR_IS_BV_CONST_NODE (real_exp))
        fputc (')', sdc->file);

      /* close bool wrapper */
      if (expect_bool && !is_boolean (sdc, real_exp)) fputc (')', sdc->file);

      /* close zero extend wrapper */
      if (zero_extend) fputc (')', sdc->file);
    }
  }
  assert (BTOR_EMPTY_STACK (expect_bv_stack));
  BTOR_RELEASE_STACK (mm, args);
  BTOR_RELEASE_STACK (mm, dump);
  BTOR_RELEASE_STACK (mm, expect_bv_stack);
  BTOR_RELEASE_STACK (mm, expect_bool_stack);
  BTOR_RELEASE_STACK (mm, add_space_stack);
  BTOR_RELEASE_STACK (mm, zero_extend_stack);
  btor_delete_ptr_hash_table (visited);
}

static void
dump_let_smt (BtorSMTDumpContext *sdc, BtorNode *exp)
{
  assert (sdc);
  assert (BTOR_IS_REGULAR_NODE (exp));
  assert (!btor_find_in_ptr_hash_table (sdc->dumped, exp));

  fputs ("(let (", sdc->file);
  if (sdc->version > 1) fputc ('(', sdc->file);
  dump_smt_id (sdc, exp);  // TODO (ma): better symbol for lets?
  fputc (' ', sdc->file);
  recursively_dump_exp_smt (sdc, exp, !is_boolean (sdc, exp));
  fputc (')', sdc->file);
  if (sdc->version == 1)
    fputc ('\n', sdc->file);
  else
    fputc (')', sdc->file);
  sdc->open_lets++;
  assert (btor_find_in_ptr_hash_table (sdc->dumped, exp));
}

static void
dump_fun_let_smt2 (BtorSMTDumpContext *sdc, BtorNode *exp)
{
  assert (sdc);
  assert (sdc->version == 2);
  assert (BTOR_IS_REGULAR_NODE (exp));
  assert (!btor_find_in_ptr_hash_table (sdc->dumped, exp));

  int is_bool;

  is_bool = is_boolean (sdc, exp);
  fputs ("(define-fun ", sdc->file);
  dump_smt_id (sdc, exp);
  fputs (" () ", sdc->file);
  // TODO (ma): workaround for now until dump_sort_smt merged from aina
  if (is_bool)
    fputs ("Bool", sdc->file);
  else
    btor_dump_sort_smt_node (exp, sdc->version, sdc->file);
  fputc (' ', sdc->file);
  recursively_dump_exp_smt (sdc, exp, !is_bool);
  fputs (")\n", sdc->file);
  assert (btor_find_in_ptr_hash_table (sdc->dumped, exp));
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
  assert (!btor_find_in_ptr_hash_table (sdc->dumped, fun));

  int i, refs;
  BtorNode *cur, *param, *fun_body, *p;
  BtorMemMgr *mm = sdc->btor->mm;
  BtorNodePtrStack visit, shared;
  BtorNodeIterator it, iit;
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
  fun_body = BTOR_LAMBDA_GET_BODY (fun);
  BTOR_PUSH_STACK (mm, visit, fun_body);
  while (!BTOR_EMPTY_STACK (visit))
  {
    cur = BTOR_REAL_ADDR_NODE (BTOR_POP_STACK (visit));

    if (btor_find_in_ptr_hash_table (mark, cur)
        || btor_find_in_ptr_hash_table (sdc->dumped, cur)
        || BTOR_IS_LAMBDA_NODE (cur))
      continue;

    b = btor_find_in_ptr_hash_table (sdc->dump, cur);
    assert (b);
    refs = b->data.asInt;

    /* args and params are handled differently */
    /* collect shared parameterized expressions in function body.
     * arguments, parameters, and constants are excluded. */
    if (!BTOR_IS_ARGS_NODE (cur)
        && !BTOR_IS_PARAM_NODE (cur)
        /* constants are always printed */
        && !BTOR_IS_BV_CONST_NODE (cur) && cur->parameterized && refs > 1)
      BTOR_PUSH_STACK (mm, shared, cur);

    btor_insert_in_ptr_hash_table (mark, cur);
    for (i = 0; i < cur->arity; i++) BTOR_PUSH_STACK (mm, visit, cur->e[i]);
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
    if (!btor_find_in_ptr_hash_table (mark, cur))
      btor_insert_in_ptr_hash_table (mark, cur);
    if (!btor_find_in_ptr_hash_table (mark, param))
      btor_insert_in_ptr_hash_table (mark, param);
    btor_insert_in_ptr_hash_table (sdc->dumped, cur);
    btor_insert_in_ptr_hash_table (sdc->dumped, param);
    if (fun != cur) fputc (' ', sdc->file);
    fputc ('(', sdc->file);
    dump_smt_id (sdc, param);
    fputc (' ', sdc->file);
    btor_dump_sort_smt_node (param, sdc->version, sdc->file);
    fputc (')', sdc->file);
  }
  fputs (") ", sdc->file);

  // TODO (ma): again wait for aina merge for dump_sort_smt
  if (is_boolean (sdc, fun_body))
    fputs ("Bool", sdc->file);
  else
    btor_dump_sort_smt_node (fun, sdc->version, sdc->file);
  fputc (' ', sdc->file);

  assert (sdc->open_lets == 0);

  /* dump expressions that are shared in 'fun' */
  if (shared.start)
    qsort (shared.start,
           BTOR_COUNT_STACK (shared),
           sizeof (BtorNode *),
           cmp_node_id);

  for (i = 0; i < BTOR_COUNT_STACK (shared); i++)
  {
    cur = BTOR_PEEK_STACK (shared, i);
    assert (BTOR_IS_REGULAR_NODE (cur));
    assert (cur->parameterized);
    dump_let_smt (sdc, cur);
    fputc (' ', sdc->file);
  }
  recursively_dump_exp_smt (sdc, fun_body, !is_boolean (sdc, fun_body));

  /* close lets */
  for (i = 0; i < sdc->open_lets; i++) fputc (')', sdc->file);
  sdc->open_lets = 0;

  /* close define-fun */
  fputs (")\n", sdc->file);

  /* due to lambda hashing it is possible that a lambda in 'fun' is shared in
   * different functions. hence, we have to check if all lambda parents of
   * the resp. lambda have already been dumped as otherwise all expressions
   * below have to be removed from 'sdc->dumped' as they will be dumped
   * again in a different function definition. */
  init_lambda_iterator (&it, fun);
  while (has_next_lambda_iterator (&it))
  {
    cur = next_lambda_iterator (&it);
    init_full_parent_iterator (&iit, cur);
    while (has_next_parent_full_parent_iterator (&iit))
    {
      p = next_parent_full_parent_iterator (&iit);
      /* find lambda parent that needs to be dumped but has not yet been
       * dumped */
      if (btor_find_in_ptr_hash_table (sdc->dump, p)
          && !btor_find_in_ptr_hash_table (sdc->dumped, p)
          && BTOR_IS_LAMBDA_NODE (p))
      {
        BTOR_PUSH_STACK (mm, visit, cur);
        while (!BTOR_EMPTY_STACK (visit))
        {
          cur = BTOR_REAL_ADDR_NODE (BTOR_POP_STACK (visit));
          assert (BTOR_IS_REGULAR_NODE (cur));

          if (!cur->parameterized
              && (!btor_find_in_ptr_hash_table (mark, cur)
                  || !btor_find_in_ptr_hash_table (sdc->dumped, cur)))
            continue;

          if (btor_find_in_ptr_hash_table (sdc->dumped, cur))
            btor_remove_from_ptr_hash_table (sdc->dumped, cur, 0, 0);

          for (i = 0; i < cur->arity; i++)
            BTOR_PUSH_STACK (mm, visit, cur->e[i]);
        }
        break;
      }
    }
  }

  BTOR_RELEASE_STACK (mm, shared);
  BTOR_RELEASE_STACK (mm, visit);
  btor_delete_ptr_hash_table (mark);
}

static void
dump_declare_fun_smt (BtorSMTDumpContext *sdc, BtorNode *exp)
{
  assert (!btor_find_in_ptr_hash_table (sdc->dumped, exp));
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
  btor_insert_in_ptr_hash_table (sdc->dumped, exp);
}

static void
dump_assert_smt2 (BtorSMTDumpContext *sdc, BtorNode *exp)
{
  assert (sdc);
  assert (sdc->version == 2);
  assert (exp);
  assert (btor_get_exp_width (sdc->btor, exp) == 1);

  fputs ("(assert ", sdc->file);
  if (!is_boolean (sdc, exp)) fputs ("(distinct ", sdc->file);
  recursively_dump_exp_smt (sdc, exp, 0);
  if (!is_boolean (sdc, exp)) fputs (" #b0)", sdc->file);
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
  if (!is_boolean (sdc, exp)) fputs ("(not (= ", sdc->file);
  recursively_dump_exp_smt (sdc, exp, 0);
  if (!is_boolean (sdc, exp))
    fprintf (sdc->file, " bv0[%d]))", btor_get_exp_width (sdc->btor, exp));
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
    /* argument nodes are counted differently */
    if (!b || BTOR_IS_ARGS_NODE (cur)) continue;
    refs++;
  }
  return refs;
}

static int
has_lambda_parent (BtorNode *exp)
{
  BtorNode *p;
  BtorNodeIterator it;
  init_full_parent_iterator (&it, exp);
  while (has_next_parent_full_parent_iterator (&it))
  {
    p = next_parent_full_parent_iterator (&it);
    if (BTOR_IS_LAMBDA_NODE (p)) return 1;
  }
  return 0;
}

static int
has_lambda_parents_only (BtorNode *exp)
{
  BtorNode *p;
  BtorNodeIterator it;
  init_full_parent_iterator (&it, exp);
  while (has_next_parent_full_parent_iterator (&it))
  {
    p = next_parent_full_parent_iterator (&it);
    if (!BTOR_IS_LAMBDA_NODE (p)) return 0;
  }
  return 1;
}

static void
dump_smt (BtorSMTDumpContext *sdc)
{
  assert (sdc);

  int i, j, not_bool;
  BtorNode *e, *cur;
  BtorMemMgr *mm;
  BtorNodePtrStack visit, all, vars, arrays, shared, ufs;
  BtorPtrHashBucket *b;
  BtorHashTableIterator it;
  BtorArgsIterator ait;

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
    cur = next_node_hash_table_iterator (&it);
    BTOR_PUSH_STACK (mm, visit, BTOR_REAL_ADDR_NODE (cur));
  }

  /* collect constants, variables, array variables and functions */
  while (!BTOR_EMPTY_STACK (visit))
  {
    cur = BTOR_POP_STACK (visit);
    assert (BTOR_IS_REGULAR_NODE (cur));
    assert (!btor_find_in_ptr_hash_table (sdc->dumped, cur));

    if (btor_find_in_ptr_hash_table (sdc->dump, cur)) continue;

    btor_insert_in_ptr_hash_table (sdc->dump, cur)->data.asInt = 0;
    BTOR_PUSH_STACK (mm, all, cur);

    if (BTOR_IS_BV_VAR_NODE (cur))
      BTOR_PUSH_STACK (mm, vars, cur);
    else if (BTOR_IS_UF_ARRAY_NODE (cur))
      BTOR_PUSH_STACK (mm, arrays, cur);
    else if (BTOR_IS_UF_NODE (cur))
      BTOR_PUSH_STACK (mm, ufs, cur);
    else if (BTOR_IS_LAMBDA_NODE (cur) && !cur->parameterized
             && !has_lambda_parents_only (cur))
      BTOR_PUSH_STACK (mm, shared, cur);

    for (j = 0; j < cur->arity; j++)
      BTOR_PUSH_STACK (mm, visit, BTOR_REAL_ADDR_NODE (cur->e[j]));
  }

  /* compute reference counts of expressions (required for determining shared
   * expressions)*/
  if (all.start)
    qsort (all.start, BTOR_COUNT_STACK (all), sizeof e, cmp_node_id);

  for (i = 0; i < BTOR_COUNT_STACK (all); i++)
  {
    cur = BTOR_PEEK_STACK (all, i);
    b   = btor_find_in_ptr_hash_table (sdc->dump, cur);
    assert (b);
    assert (b->data.asInt == 0);
    /* cache result for later reuse */
    b->data.asInt = get_references (sdc, cur);

    /* update references for expressions under argument nodes */
    if (BTOR_IS_ARGS_NODE (cur) && b->data.asInt > 0)
    {
      init_args_iterator (&ait, cur);
      while (has_next_args_iterator (&ait))
      {
        e = BTOR_REAL_ADDR_NODE (next_args_iterator (&ait));
        assert (btor_find_in_ptr_hash_table (sdc->dump, e));
        btor_find_in_ptr_hash_table (sdc->dump, e)->data.asInt += b->data.asInt;
      }
    }
  }

  /* collect globally shared expressions */
  for (i = 0; i < BTOR_COUNT_STACK (all); i++)
  {
    cur = BTOR_PEEK_STACK (all, i);
    b   = btor_find_in_ptr_hash_table (sdc->dump, cur);
    assert (b);

    if (b->data.asInt <= 1
        /* parameterized expressions are only shared within a function */
        || cur->parameterized
        || BTOR_IS_PARAM_NODE (cur)
        /* constants are always printed */
        || BTOR_IS_BV_CONST_NODE (cur)
        /* for variables and functions the resp. symbols are always printed */
        || BTOR_IS_BV_VAR_NODE (cur)
        || BTOR_IS_FUN_NODE (cur)
        /* argument nodes are never printed */
        || BTOR_IS_ARGS_NODE (cur))
      continue;

    BTOR_PUSH_STACK (mm, shared, cur);
  }

  /* collect boolean terms */
  for (i = 0; i < BTOR_COUNT_STACK (all); i++)
  {
    cur = BTOR_PEEK_STACK (all, i);

    /* these nodes are boolean by definition */
    if (BTOR_IS_BV_EQ_NODE (cur) || BTOR_IS_FUN_EQ_NODE (cur)
        || BTOR_IS_ULT_NODE (cur)
        || cur == BTOR_REAL_ADDR_NODE (sdc->btor->true_exp))
    {
      btor_insert_in_ptr_hash_table (sdc->boolean, cur);
      continue;
    }
    else if (BTOR_IS_APPLY_NODE (cur))
    {
      /* boolean function */
      if ((BTOR_IS_LAMBDA_NODE (cur->e[0])
           && is_boolean (sdc, BTOR_LAMBDA_GET_BODY (cur->e[0])))
          || (BTOR_IS_UF_NODE (cur->e[0])
              && btor_is_bool_sort (
                     &sdc->btor->sorts_unique_table,
                     btor_get_codomain_fun_sort (&sdc->btor->sorts_unique_table,
                                                 cur->e[0]->sort_id))))
        btor_insert_in_ptr_hash_table (sdc->boolean, cur);
      continue;
    }
    else if (btor_get_exp_width (sdc->btor, cur) == 1
             && (BTOR_IS_AND_NODE (cur) || BTOR_IS_BV_COND_NODE (cur)))
    {
      not_bool = 0;
      for (j = 0; j < cur->arity; j++)
      {
        if (!is_boolean (sdc, cur->e[j]))
        {
          not_bool = 1;
          break;
        }
      }

      if (not_bool) continue;

      btor_insert_in_ptr_hash_table (sdc->boolean, cur);
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

    if (btor_find_in_ptr_hash_table (sdc->dumped, cur)) continue;

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
    assert (btor_find_in_ptr_hash_table (sdc->dumped, cur));
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

    if (temp->parameterized && !has_lambda_parent (temp))
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
