/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2013 Armin Biere.
 *  Copyright (C) 2012-2017 Mathias Preiner.
 *  Copyright (C) 2012-2017 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btorcore.h"
#include "btorexit.h"
#include "btorexp.h"
#include "btorsort.h"
#include "utils/btorhashint.h"
#include "utils/btorhashptr.h"
#ifndef NDEBUG
#include "btorclone.h"
#endif
#include "utils/btorhashptr.h"
#include "utils/btornodeiter.h"

#include "btordumpsmt.h"

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
  uint32_t maxid;
  uint32_t pretty_print;
  uint32_t open_lets;
  uint32_t indent;
  bool newline;
};

typedef struct BtorSMTDumpContext BtorSMTDumpContext;

static BtorSMTDumpContext *
new_smt_dump_context (Btor *btor, FILE *file)
{
  BtorSMTDumpContext *sdc;
  BTOR_CNEW (btor->mm, sdc);

  sdc->btor        = btor;
  sdc->dump        = btor_hashptr_table_new (btor->mm,
                                      (BtorHashPtr) btor_node_hash_by_id,
                                      (BtorCmpPtr) btor_node_compare_by_id);
  sdc->dumped      = btor_hashptr_table_new (btor->mm,
                                        (BtorHashPtr) btor_node_hash_by_id,
                                        (BtorCmpPtr) btor_node_compare_by_id);
  sdc->boolean     = btor_hashptr_table_new (btor->mm,
                                         (BtorHashPtr) btor_node_hash_by_id,
                                         (BtorCmpPtr) btor_node_compare_by_id);
  sdc->stores      = btor_hashptr_table_new (btor->mm,
                                        (BtorHashPtr) btor_node_hash_by_id,
                                        (BtorCmpPtr) btor_node_compare_by_id);
  sdc->idtab       = btor_hashptr_table_new (btor->mm,
                                       (BtorHashPtr) btor_node_hash_by_id,
                                       (BtorCmpPtr) btor_node_compare_by_id);
  sdc->const_cache = btor_hashptr_table_new (
      btor->mm, (BtorHashPtr) btor_bv_hash, (BtorCmpPtr) btor_bv_compare);
  /* use pointer for hashing and comparison */
  sdc->roots        = btor_hashptr_table_new (btor->mm, 0, 0);
  sdc->file         = file;
  sdc->maxid        = 1;
  sdc->pretty_print = btor_opt_get (btor, BTOR_OPT_PRETTY_PRINT);
  sdc->newline      = sdc->pretty_print == 1;
  return sdc;
}

static void
delete_smt_dump_context (BtorSMTDumpContext *sdc)
{
  BtorPtrHashTableIterator it;

  btor_hashptr_table_delete (sdc->dump);
  btor_hashptr_table_delete (sdc->dumped);
  btor_hashptr_table_delete (sdc->boolean);
  btor_hashptr_table_delete (sdc->stores);
  btor_hashptr_table_delete (sdc->idtab);

  btor_iter_hashptr_init (&it, sdc->roots);
  while (btor_iter_hashptr_has_next (&it))
    btor_node_release (sdc->btor, btor_iter_hashptr_next (&it));
  btor_hashptr_table_delete (sdc->roots);

  btor_iter_hashptr_init (&it, sdc->const_cache);
  while (btor_iter_hashptr_has_next (&it))
  {
    assert (it.bucket->data.as_str);
    btor_mem_freestr (sdc->btor->mm, it.bucket->data.as_str);
    btor_bv_free (sdc->btor->mm,
                  (BtorBitVector *) btor_iter_hashptr_next (&it));
  }
  btor_hashptr_table_delete (sdc->const_cache);
  BTOR_DELETE (sdc->btor->mm, sdc);
}

static void
add_root_to_smt_dump_context (BtorSMTDumpContext *sdc, BtorNode *root)
{
  if (!btor_hashptr_table_get (sdc->roots, root))
    btor_hashptr_table_add (sdc->roots, btor_node_copy (sdc->btor, root));
}

static int32_t
cmp_node_id (const void *p, const void *q)
{
  BtorNode *a = *(BtorNode **) p;
  BtorNode *b = *(BtorNode **) q;
  return a->id - b->id;
}

static uint32_t
smt_id (BtorSMTDumpContext *sdc, BtorNode *exp)
{
  assert (sdc);
  assert (exp);
  assert (btor_node_is_regular (exp));

  BtorPtrHashBucket *b;
  int32_t id;

  if (sdc->pretty_print)
  {
    b = btor_hashptr_table_get (sdc->idtab, exp);

    if (!b)
    {
      b              = btor_hashptr_table_add (sdc->idtab, exp);
      b->data.as_int = sdc->maxid++;
    }
    return b->data.as_int;
  }
  id = btor_node_get_btor_id (exp);
  if (id) return id;
  return exp->id;
}

static bool
symbol_needs_quotes (const char *sym)
{
  char ch;
  size_t i, len;

  len = strlen (sym);

  /* already quoted */
  if (sym[0] == '|' && sym[len - 1] == '|') return false;

  for (i = 0; i < len; i++)
  {
    ch = sym[i];
    if ((ch >= 65 && ch <= 90) || (ch >= 97 && ch <= 122)
        || (ch >= 48 && ch <= 57) || ch == '~' || ch == '!' || ch == '@'
        || ch == '$' || ch == '%' || ch == '^' || ch == '&' || ch == '*'
        || ch == '_' || ch == '-' || ch == '+' || ch == '=' || ch == '<'
        || ch == '>' || ch == '.' || ch == '?' || ch == '/')
      continue;
    return true;
  }
  return false;
}

static void
dump_smt_id (BtorSMTDumpContext *sdc, BtorNode *exp)
{
  assert (sdc);
  assert (exp);

  const char *type, *sym;

  exp = btor_node_real_addr (exp);

  switch (exp->kind)
  {
    case BTOR_VAR_NODE: type = "v"; goto DUMP_SYMBOL;

    case BTOR_PARAM_NODE:
      type = "p";
    DUMP_SYMBOL:
      sym = btor_node_get_symbol (sdc->btor, exp);
      if (sym && !isdigit ((int32_t) sym[0]))
      {
        if (symbol_needs_quotes (sym))
          fprintf (sdc->file, "|%s|", sym);
        else
          fputs (sym, sdc->file);
        return;
      }
      break;

    case BTOR_UF_NODE: type = "uf"; goto DUMP_SYMBOL;

    case BTOR_LAMBDA_NODE: type = "f"; goto DUMP_SYMBOL;

    default: type = "$e";
  }

  fprintf (sdc->file, "%s%u", type, smt_id (sdc, exp));
}

static bool
is_boolean (BtorSMTDumpContext *sdc, BtorNode *exp)
{
  exp = btor_node_real_addr (exp);
  return btor_hashptr_table_get (sdc->boolean, exp) != 0;
}

void
btor_dumpsmt_dump_const_value (Btor *btor,
                               const BtorBitVector *bits,
                               uint32_t base,
                               FILE *file)
{
  assert (btor);
  assert (bits);
  assert (base == BTOR_OUTPUT_BASE_BIN || base == BTOR_OUTPUT_BASE_DEC
          || base == BTOR_OUTPUT_BASE_HEX);

  char *val;

  /* SMT-LIB v1.2 only supports decimal output */
  if (base == BTOR_OUTPUT_BASE_DEC)
  {
    val = btor_bv_to_dec_char (btor->mm, bits);
    fprintf (file, "(_ bv%s %d)", val, bits->width);
  }
  else if (base == BTOR_OUTPUT_BASE_HEX && bits->width % 4 == 0)
  {
    val = btor_bv_to_hex_char (btor->mm, bits);
    fprintf (file, "#x%s", val);
  }
  else
  {
    val = btor_bv_to_char (btor->mm, bits);
    fprintf (file, "#b%s", val);
  }
  btor_mem_freestr (btor->mm, val);
}

static void
dump_const_value_aux_smt (BtorSMTDumpContext *sdc, BtorBitVector *bits)
{
  assert (sdc);
  assert (bits);

  uint32_t base;
  FILE *file;
  char *val;
  BtorPtrHashBucket *b;

  base = btor_opt_get (sdc->btor, BTOR_OPT_OUTPUT_NUMBER_FORMAT);
  file = sdc->file;

  /* converting consts to decimal/hex is costly. we now always dump the value of
   * constants. in order to avoid computing the same value again we cache
   * the result of the first computation and print the cached value in
   * subsequent calls. */
  if (base == BTOR_OUTPUT_BASE_DEC)
  {
    if ((b = btor_hashptr_table_get (sdc->const_cache, bits)))
    {
      val = b->data.as_str;
      assert (val);
    }
    else
    {
      val = btor_bv_to_dec_char (sdc->btor->mm, bits);
      btor_hashptr_table_add (sdc->const_cache,
                              btor_bv_copy (sdc->btor->mm, bits))
          ->data.as_str = val;
    }
    fprintf (file, "(_ bv%s %d)", val, bits->width);
  }
  else if (base == BTOR_OUTPUT_BASE_HEX && bits->width % 4 == 0)
  {
    if ((b = btor_hashptr_table_get (sdc->const_cache, bits)))
    {
      val = b->data.as_str;
      assert (val);
    }
    else
    {
      val = btor_bv_to_hex_char (sdc->btor->mm, bits);
      btor_hashptr_table_add (sdc->const_cache,
                              btor_bv_copy (sdc->btor->mm, bits))
          ->data.as_str = val;
    }
    fprintf (file, "#x%s", val);
  }
  else
    btor_dumpsmt_dump_const_value (sdc->btor, bits, base, file);
}

void
btor_dumpsmt_dump_sort (BtorSort *sort, FILE *file)
{
  uint32_t i;
  const char *fmt;

  switch (sort->kind)
  {
    case BTOR_BOOL_SORT: fputs ("Bool", file); break;

    case BTOR_BITVEC_SORT:
      fmt = "(_ BitVec %d)";
      fprintf (file, fmt, sort->bitvec.width);
      break;

    case BTOR_ARRAY_SORT:
      fmt = "(Array (_ BitVec %d) (_ BitVec %d))";
      assert (sort->array.index->kind == BTOR_BITVEC_SORT);
      assert (sort->array.element->kind == BTOR_BITVEC_SORT);
      fprintf (file,
               fmt,
               sort->array.index->bitvec.width,
               sort->array.element->bitvec.width);
      break;

    case BTOR_FUN_SORT:
      /* print domain */
      fputc ('(', file);
      if (sort->fun.domain->kind == BTOR_TUPLE_SORT)
      {
        for (i = 0; i < sort->fun.domain->tuple.num_elements; i++)
        {
          btor_dumpsmt_dump_sort (sort->fun.domain->tuple.elements[i], file);
          if (i < sort->fun.domain->tuple.num_elements - 1) fputc (' ', file);
        }
      }
      else
        btor_dumpsmt_dump_sort (sort->fun.domain, file);
      fputc (')', file);
      fputc (' ', file);

      /* print co-domain */
      btor_dumpsmt_dump_sort (sort->fun.codomain, file);
      break;

    default: assert (0);
  }
}

void
btor_dumpsmt_dump_sort_node (BtorNode *exp, FILE *file)
{
  assert (exp);
  assert (file);

  Btor *btor;
  BtorSortId s_fid, s_tid, s_cid, s_did;
  BtorSort *sort;

  exp  = btor_node_real_addr (exp);
  btor = exp->btor;
  if (btor_node_is_array (exp))
  {
    s_fid = btor_node_get_sort_id (exp);
    s_tid = btor_sort_fun_get_domain (btor, s_fid);
    assert (btor_sort_is_tuple (btor, s_tid));
    s_did = btor_sort_get_by_id (btor, s_tid)->tuple.elements[0]->id;
    s_cid = btor_sort_fun_get_codomain (btor, s_fid);
    fprintf (file,
             "(Array (_ BitVec %d) (_ BitVec %d))",
             btor_sort_bv_get_width (btor, s_did),
             btor_sort_bv_get_width (btor, s_cid));
  }
  else
  {
    sort = btor_sort_get_by_id (exp->btor, btor_node_get_sort_id (exp));
    btor_dumpsmt_dump_sort (sort, file);
  }
}

#if 0
static void
extract_store (BtorSMTDumpContext * sdc, BtorNode * exp,
	       BtorNode ** index, BtorNode ** value, BtorNode ** array)
{
  BtorNode *ite, *eq, *apply;

  if (!btor_node_is_lambda (exp))
    return;

  if (((BtorLambdaNode *) exp)->num_params != 1)
    return;

  if (!btor_node_is_bv_cond (exp->e[1]))
    return;

  ite = exp->e[1];
  if (btor_node_is_inverted (ite))
    return;

  if (!btor_node_is_bv_eq (ite->e[0]))
    return;

  /* check ite condition */
  eq = ite->e[0];
  if (btor_node_is_inverted (eq))
    return;

  if (!eq->parameterized)
    return;

  /* check if branch */
  if (btor_node_real_addr (ite->e[1])->parameterized)
    return;

  /* check else branch */
  if (!btor_node_real_addr (ite->e[2])->parameterized)
    return;

  if (!btor_node_is_apply (ite->e[2]))
    return;

  apply = ite->e[2];
  if (btor_node_is_inverted (apply))
    return;

  if (!btor_node_is_uf_array (apply->e[0])
      && !btor_hashptr_table_get (sdc->stores, apply->e[0]))
    return;

  if (!btor_node_is_param (apply->e[1]->e[0]))
    return;

  *index = btor_node_real_addr (eq->e[0])->parameterized ? eq->e[1] : eq->e[0];
  *value = ite->e[1];
  *array = apply->e[0];
}
#endif

#define PUSH_DUMP_NODE(                                      \
    exp, expect_bv, expect_bool, add_space, zero_ext, depth) \
  {                                                          \
    BTOR_PUSH_STACK (dump, exp);                             \
    BTOR_PUSH_STACK (expect_bv_stack, expect_bv);            \
    BTOR_PUSH_STACK (expect_bool_stack, expect_bool);        \
    BTOR_PUSH_STACK (add_space_stack, add_space);            \
    BTOR_PUSH_STACK (zero_extend_stack, zero_ext);           \
    BTOR_PUSH_STACK (depth_stack, depth);                    \
  }

static const char *g_kind2smt[BTOR_NUM_OPS_NODE] = {
    [BTOR_INVALID_NODE]   = "invalid",
    [BTOR_CONST_NODE]     = "const",
    [BTOR_VAR_NODE]       = "var",
    [BTOR_PARAM_NODE]     = "param",
    [BTOR_BV_SLICE_NODE]  = "extract",
    [BTOR_BV_AND_NODE]    = "bvand",
    [BTOR_FUN_EQ_NODE]    = "=",
    [BTOR_BV_EQ_NODE]     = "=",
    [BTOR_BV_ADD_NODE]    = "bvadd",
    [BTOR_BV_MUL_NODE]    = "bvmul",
    [BTOR_BV_ULT_NODE]    = "bvult",
    [BTOR_BV_SLL_NODE]    = "bvshl",
    [BTOR_BV_SRL_NODE]    = "bvlshr",
    [BTOR_BV_UDIV_NODE]   = "bvudiv",
    [BTOR_BV_UREM_NODE]   = "bvurem",
    [BTOR_BV_CONCAT_NODE] = "concat",
    [BTOR_APPLY_NODE]     = "apply",
    [BTOR_LAMBDA_NODE]    = "lambda",
    [BTOR_COND_NODE]      = "ite",
    [BTOR_ARGS_NODE]      = "args",
    [BTOR_UF_NODE]        = "uf",
    [BTOR_PROXY_NODE]     = "proxy"};

static void
collect_and_children (BtorSMTDumpContext *sdc,
                      BtorNode *exp,
                      BtorNodePtrStack *children)
{
  assert (children);
  assert (BTOR_EMPTY_STACK (*children));
  assert (btor_node_is_bv_and (exp));

  bool skip;
  uint32_t i;
  int32_t id;
  BtorNode *cur, *real_cur;
  BtorNodePtrQueue visit;
  BtorPtrHashBucket *b;
  BtorIntHashTable *cache;

  cache = btor_hashint_table_new (sdc->btor->mm);

  /* get children of multi-input and */
  BTOR_INIT_QUEUE (sdc->btor->mm, visit);
  for (i = 0; i < btor_node_real_addr (exp)->arity; i++)
    BTOR_ENQUEUE (visit, btor_node_real_addr (exp)->e[i]);
  while (!BTOR_EMPTY_QUEUE (visit))
  {
    cur      = BTOR_DEQUEUE (visit);
    real_cur = btor_node_real_addr (cur);
    id       = btor_node_get_id (cur);

    skip = btor_hashint_table_contains (cache, id);
    if (!skip)
    {
      btor_hashint_table_add (cache, id);
      b = btor_hashptr_table_get (sdc->dump, real_cur);
    }
    else
      b = 0;

    if (!btor_node_is_bv_and (real_cur) || (b && b->data.as_int > 1)
        || btor_node_is_inverted (cur) || skip)
    {
      BTOR_PUSH_STACK (*children, cur);
      continue;
    }

    assert (!btor_hashptr_table_get (sdc->dumped, real_cur));
    btor_hashptr_table_add (sdc->dumped, real_cur);
    for (i = 0; i < real_cur->arity; i++) BTOR_ENQUEUE (visit, real_cur->e[i]);
  }
  BTOR_RELEASE_QUEUE (visit);
  btor_hashint_table_delete (cache);
}

static void
print_indent (BtorSMTDumpContext *sdc)
{
  uint32_t i;
  for (i = 0; i < sdc->indent; i++) fputc (' ', sdc->file);
}

static inline void
open_sexp (BtorSMTDumpContext *sdc)
{
  if (sdc->pretty_print && sdc->indent > 0 && sdc->newline)
  {
    fputc ('\n', sdc->file);
    print_indent (sdc);
  }
  fputc ('(', sdc->file);
  sdc->indent++;
}

static inline void
close_sexp (BtorSMTDumpContext *sdc)
{
  fputc (')', sdc->file);
  sdc->indent--;
}

static void recursively_dump_exp_let_smt (BtorSMTDumpContext *sdc,
                                          BtorNode *exp,
                                          bool expect_bv,
                                          uint32_t depth_limit);

static void
expand_lambda (BtorSMTDumpContext *sdc,
               BtorNode *exp,
               BtorNodePtrStack *indices,
               BtorNodePtrStack *values,
               BtorNode **base_array)
{
  assert (btor_node_is_lambda (exp));
  assert (btor_node_is_array (exp));

  uint32_t i;
  BtorPtrHashTableIterator it;
  BtorPtrHashTable *static_rho;
  BtorNode *index, *value, *cur;
  BtorNodePtrStack visit;
  BtorIntHashTable *cache;

  BTOR_INIT_STACK (sdc->btor->mm, visit);

  cache = btor_hashint_table_new (sdc->btor->mm);

  *base_array = 0;
  BTOR_PUSH_STACK (visit, exp);
  while (!BTOR_EMPTY_STACK (visit))
  {
    cur = btor_node_real_addr (BTOR_POP_STACK (visit));

    if (btor_hashint_table_contains (cache, cur->id)
        || (!cur->parameterized && !btor_node_is_array (cur)))
      continue;

    btor_hashint_table_add (cache, cur->id);

    if (btor_node_is_lambda (cur))
    {
      assert (btor_node_is_array (cur));
      static_rho = btor_node_lambda_get_static_rho (cur);
      assert (static_rho);

      btor_iter_hashptr_init (&it, static_rho);
      while (btor_iter_hashptr_has_next (&it))
      {
        value = it.bucket->data.as_ptr;
        index = btor_iter_hashptr_next (&it);
        assert (btor_node_is_args (index));
        assert (btor_node_args_get_arity (sdc->btor, index) == 1);
        BTOR_PUSH_STACK (*indices, index->e[0]);
        BTOR_PUSH_STACK (*values, value);
      }
    }
    else if (btor_node_is_array (cur))
    {
      assert (!*base_array);
      *base_array = cur;
      continue;
    }

    if (!btor_hashptr_table_get (sdc->dumped, cur))
      btor_hashptr_table_add (sdc->dumped, cur);

    for (i = 0; i < cur->arity; i++) BTOR_PUSH_STACK (visit, cur->e[i]);
  }
  assert (*base_array);
  BTOR_RELEASE_STACK (visit);
  btor_hashint_table_delete (cache);
}

static void
recursively_dump_exp_smt (BtorSMTDumpContext *sdc,
                          BtorNode *exp,
                          int32_t expect_bv,
                          uint32_t depth_limit)
{
  assert (sdc);
  assert (exp);
  assert (btor_hashptr_table_get (sdc->dump, btor_node_real_addr (exp)));

  uint32_t depth;
  bool is_bool, expect_bool;
  uint32_t pad, i, zero_extend;
  int32_t add_space;
  BtorBitVector *bits;
  const char *op, *fmt;
  BtorNode *tmp, *real_exp;
  BtorArgsIterator it;
  BtorNodeIterator node_it;
  BtorNodePtrStack dump, args, indices, values;
  BtorIntStack expect_bv_stack, expect_bool_stack, depth_stack;
  BtorIntStack add_space_stack, zero_extend_stack;
  BtorPtrHashTable *visited;
  BtorMemMgr *mm;

  mm      = sdc->btor->mm;
  visited = btor_hashptr_table_new (mm, 0, 0);
  BTOR_INIT_STACK (mm, args);
  BTOR_INIT_STACK (mm, dump);
  BTOR_INIT_STACK (mm, expect_bv_stack);
  BTOR_INIT_STACK (mm, expect_bool_stack);
  BTOR_INIT_STACK (mm, add_space_stack);
  BTOR_INIT_STACK (mm, zero_extend_stack);
  BTOR_INIT_STACK (mm, depth_stack);
  BTOR_INIT_STACK (mm, indices);
  BTOR_INIT_STACK (mm, values);

  PUSH_DUMP_NODE (exp, expect_bv, 0, 0, 0, 0);
  while (!BTOR_EMPTY_STACK (dump))
  {
    assert (!BTOR_EMPTY_STACK (expect_bv_stack));
    assert (!BTOR_EMPTY_STACK (expect_bool_stack));
    assert (!BTOR_EMPTY_STACK (add_space_stack));
    assert (!BTOR_EMPTY_STACK (zero_extend_stack));
    assert (!BTOR_EMPTY_STACK (depth_stack));
    assert (BTOR_COUNT_STACK (expect_bv_stack)
            == BTOR_COUNT_STACK (expect_bool_stack));
    assert (BTOR_COUNT_STACK (expect_bool_stack)
            == BTOR_COUNT_STACK (add_space_stack));
    assert (BTOR_COUNT_STACK (add_space_stack)
            == BTOR_COUNT_STACK (zero_extend_stack));
    assert (BTOR_COUNT_STACK (zero_extend_stack)
            == BTOR_COUNT_STACK (depth_stack));
    depth       = BTOR_POP_STACK (depth_stack);
    exp         = BTOR_POP_STACK (dump);
    expect_bv   = BTOR_POP_STACK (expect_bv_stack);
    expect_bool = BTOR_POP_STACK (expect_bool_stack);
    add_space   = BTOR_POP_STACK (add_space_stack);
    zero_extend = BTOR_POP_STACK (zero_extend_stack);
    real_exp    = btor_node_real_addr (exp);
    is_bool     = is_boolean (sdc, real_exp);
    assert (!expect_bv || !expect_bool);
    assert (!expect_bool || !expect_bv);

    /* open s-expression */
    if (!btor_hashptr_table_get (visited, real_exp))
    {
      if (add_space) fputc (' ', sdc->file);

      /* wrap node with zero_extend */
      if (zero_extend)
      {
        fputc (' ', sdc->file);
        open_sexp (sdc);
        fprintf (sdc->file, "(_ zero_extend %d) ", zero_extend);
      }

      /* always print constants */
      if (btor_node_is_bv_const (real_exp))
      {
        if (exp == sdc->btor->true_exp && !expect_bv)
          fputs ("true", sdc->file);
        else if (exp == btor_node_invert (sdc->btor->true_exp) && !expect_bv)
          fputs ("false", sdc->file);
        else if (btor_node_is_inverted (exp))
        {
          bits = btor_bv_not (sdc->btor->mm,
                              btor_node_bv_const_get_bits (real_exp));
          dump_const_value_aux_smt (sdc, bits);
          btor_bv_free (sdc->btor->mm, bits);
        }
        else
        {
          dump_const_value_aux_smt (sdc,
                                    btor_node_bv_const_get_bits (real_exp));
        }

        /* close zero extend */
        if (zero_extend) close_sexp (sdc);
        continue;
      }

      /* wrap non-bool node and make it bool */
      if (expect_bool && !is_bool)
      {
        open_sexp (sdc);
        fputs ("= ", sdc->file);
        bits = btor_bv_one (sdc->btor->mm, 1);
        dump_const_value_aux_smt (sdc, bits);
        btor_bv_free (sdc->btor->mm, bits);
        fputc (' ', sdc->file);
      }

      /* wrap node with bvnot/not */
      if (btor_node_is_inverted (exp))
      {
        open_sexp (sdc);
        fputs (expect_bv || !is_bool ? "bvnot " : "not ", sdc->file);
      }

      /* wrap bool node and make it a bit vector expression */
      if (is_bool && expect_bv)
      {
        open_sexp (sdc);
        fputs ("ite ", sdc->file);
      }

      if (btor_hashptr_table_get (sdc->dumped, real_exp)
          || (btor_node_is_lambda (real_exp) && !btor_node_is_array (real_exp))
          || btor_node_is_uf (real_exp))
      {
#ifndef NDEBUG
        BtorPtrHashBucket *b;
        b = btor_hashptr_table_get (sdc->dump, real_exp);
        assert (b);
        /* functions and variables are declared separately */
        assert (btor_node_is_lambda (real_exp) || btor_node_is_uf (real_exp)
                || btor_node_is_bv_var (real_exp)
                || btor_node_is_param (real_exp) || b->data.as_int > 1);
#endif
        dump_smt_id (sdc, exp);
        goto CLOSE_WRAPPER;
      }

      if (depth_limit && depth >= depth_limit)
      {
        fprintf (sdc->file, "%s_%d", g_kind2smt[real_exp->kind], real_exp->id);
        goto CLOSE_WRAPPER;
      }

      PUSH_DUMP_NODE (exp, expect_bv, expect_bool, 0, zero_extend, depth);
      btor_hashptr_table_add (visited, real_exp);
      op = "";
      switch (real_exp->kind)
      {
        case BTOR_BV_SLL_NODE:
        case BTOR_BV_SRL_NODE:
          assert (!is_bool);
          op = real_exp->kind == BTOR_BV_SRL_NODE ? "bvlshr" : "bvshl";
          assert (btor_node_bv_get_width (sdc->btor, real_exp) > 1);
          pad = btor_node_bv_get_width (sdc->btor, real_exp)
                - btor_node_bv_get_width (sdc->btor, real_exp->e[1]);
          PUSH_DUMP_NODE (real_exp->e[1], 1, 0, 1, pad, depth + 1);
          PUSH_DUMP_NODE (real_exp->e[0], 1, 0, 1, 0, depth + 1);
          break;

        case BTOR_COND_NODE:
          op = "ite";
          PUSH_DUMP_NODE (real_exp->e[2], !is_bool, 0, 1, 0, depth + 1);
          PUSH_DUMP_NODE (real_exp->e[1], !is_bool, 0, 1, 0, depth + 1);
          PUSH_DUMP_NODE (real_exp->e[0], 0, 1, 1, 0, depth + 1);
          break;

        case BTOR_APPLY_NODE:

          if (btor_node_is_update (real_exp->e[0])
              || btor_node_is_uf_array (real_exp->e[0]))
            op = "select ";

          /* we need the arguments in reversed order */
          btor_iter_args_init (&it, real_exp->e[1]);
          while (btor_iter_args_has_next (&it))
          {
            tmp = btor_iter_args_next (&it);
            BTOR_PUSH_STACK (args, tmp);
          }
          while (!BTOR_EMPTY_STACK (args))
          {
            tmp = BTOR_POP_STACK (args);
            // TODO (ma): what about bool arguments/indices
            PUSH_DUMP_NODE (tmp, 1, 0, 1, 0, depth + 1);
          }
          PUSH_DUMP_NODE (real_exp->e[0], 1, 0, 0, 0, depth + 1);
          break;

        case BTOR_LAMBDA_NODE:
          assert (btor_node_is_lambda (exp));
          assert (btor_node_is_array (exp));

          tmp = 0;
          expand_lambda (sdc, exp, &indices, &values, &tmp);
          assert (tmp);
          assert (btor_node_is_uf_array (tmp));

          for (i = 0; i < BTOR_COUNT_STACK (indices); i++)
          {
            PUSH_DUMP_NODE (BTOR_PEEK_STACK (values, i), 1, 0, 1, 0, depth + 1);
            PUSH_DUMP_NODE (
                BTOR_PEEK_STACK (indices, i), 1, 0, 1, 0, depth + 1);
            if (i < BTOR_COUNT_STACK (indices) - 1)
            {
              open_sexp (sdc);
              fputs ("store ", sdc->file);
              PUSH_DUMP_NODE (exp, 1, 0, 1, 0, depth + 1);
            }
          }
          BTOR_RESET_STACK (indices);
          BTOR_RESET_STACK (values);

          op = "store";
          /* push base array */
          PUSH_DUMP_NODE (tmp, 1, 0, 1, 0, depth + 1);
          break;

        case BTOR_UPDATE_NODE:
          op = "store";
          PUSH_DUMP_NODE (real_exp->e[2], 1, 0, 1, 0, depth + 1);
          PUSH_DUMP_NODE (real_exp->e[1]->e[0], 1, 0, 1, 0, depth + 1);
          PUSH_DUMP_NODE (real_exp->e[0], 1, 0, 1, 0, depth + 1);
          break;

        default:
          expect_bv = 1;
          switch (real_exp->kind)
          {
            case BTOR_FUN_EQ_NODE:
            case BTOR_BV_EQ_NODE:
              op        = "=";
              expect_bv = 1;
              break;
            case BTOR_BV_ULT_NODE:
              op        = "bvult";
              expect_bv = 1;
              break;
            case BTOR_BV_SLICE_NODE:
              assert (!is_bool);
              op = "(_ extract ";
              break;
            case BTOR_BV_AND_NODE:
              op        = is_bool ? "and" : "bvand";
              expect_bv = !is_bool;
              break;
            case BTOR_BV_ADD_NODE:
              assert (!is_bool);
              op = "bvadd";
              break;
            case BTOR_BV_MUL_NODE:
              assert (!is_bool);
              op = "bvmul";
              break;
            case BTOR_BV_UDIV_NODE:
              assert (!is_bool);
              op = "bvudiv";
              break;
            case BTOR_BV_UREM_NODE:
              assert (!is_bool);
              op = "bvurem";
              break;
            case BTOR_BV_CONCAT_NODE:
              assert (!is_bool);
              op = "concat";
              break;
            case BTOR_FORALL_NODE:
              assert (is_bool);
              op = "forall";
              break;
            case BTOR_EXISTS_NODE:
              assert (is_bool);
              op = "exists";
              break;
            default: assert (0); op = "unknown";
          }
          if (btor_node_is_bv_and (real_exp) && is_bool)
          {
            assert (BTOR_EMPTY_STACK (args));
            collect_and_children (sdc, exp, &args);
            assert (BTOR_COUNT_STACK (args) >= 2);
            for (i = 0; i < BTOR_COUNT_STACK (args); i++)
            {
              tmp = BTOR_PEEK_STACK (args, i);
              PUSH_DUMP_NODE (tmp, expect_bv, 0, 1, 0, depth + 1);
            }
            BTOR_RESET_STACK (args);
          }
#if 0
		else if (btor_node_is_quantifier (real_exp))
		  {
		    /* body of quantifiers are handled differently (let
		     * bindings etc.) */
		    if (real_exp->e[1] != btor_node_binder_get_body (real_exp)
			&& real_exp->kind
			   != btor_node_real_addr (real_exp->e[1])->kind)
		      PUSH_DUMP_NODE (real_exp->e[1], 0, 1, 1, 0,
				      depth + 1);
		  }
#endif
          else if (!btor_node_is_quantifier (real_exp))
            for (i = 1; i <= real_exp->arity; i++)
              PUSH_DUMP_NODE (real_exp->e[real_exp->arity - i],
                              expect_bv,
                              0,
                              1,
                              0,
                              depth + 1);
      }

      /* open s-expression */
      assert (op);
      open_sexp (sdc);
      fprintf (sdc->file, "%s", op);

      if (btor_node_is_bv_slice (real_exp))
      {
        fmt = "%d %d)";
        fprintf (sdc->file,
                 fmt,
                 btor_node_bv_slice_get_upper (real_exp),
                 btor_node_bv_slice_get_lower (real_exp));
      }
      else if (btor_node_is_quantifier (real_exp))
      {
        fputs (" (", sdc->file);
        btor_iter_binder_init (&node_it, real_exp);
        tmp = 0;
        while (btor_iter_binder_has_next (&node_it))
        {
          tmp = btor_iter_binder_next (&node_it);

          if (tmp->kind != real_exp->kind) break;

          if (tmp != real_exp) fputc (' ', sdc->file);
          if (sdc->pretty_print)
          {
            fputc ('\n', sdc->file);
            print_indent (sdc);
          }
          fputc ('(', sdc->file);
          dump_smt_id (sdc, tmp->e[0]);
          fputc (' ', sdc->file);
          btor_dumpsmt_dump_sort_node (tmp->e[0], sdc->file);
          fputc (')', sdc->file);
          btor_hashptr_table_add (sdc->dumped, tmp->e[0]);
          btor_hashptr_table_add (sdc->dumped, tmp);
        }
        assert (tmp);
        assert (btor_node_is_regular (tmp));
        assert (btor_node_is_quantifier (tmp));
        fputc (')', sdc->file);

        if (tmp->kind == real_exp->kind)
        {
          assert (tmp->e[1] == btor_node_binder_get_body (tmp));
          recursively_dump_exp_let_smt (
              sdc, tmp->e[1], false, depth_limit ? depth_limit - depth : 0);
        }
        else
          PUSH_DUMP_NODE (tmp, 0, 1, 1, 0, depth + 1);

#if 0
	      fprintf (sdc->file, " ((%s ",
		       btor_get_symbol_exp (sdc->btor, real_exp->e[0]));
	      btor_dumpsmt_dump_sort_node (real_exp->e[0], sdc->file);
	      fprintf (sdc->file, "))");
	      btor_hashptr_table_add (sdc->dumped, real_exp->e[0]);
	      if (real_exp->e[1] == btor_node_binder_get_body (real_exp))
		recursively_dump_exp_let_smt (
		    sdc, real_exp->e[1], false,
		    depth_limit ? depth_limit - depth : 0);
#endif
      }
    }
    /* close s-expression */
    else
    {
      if (!btor_hashptr_table_get (sdc->dumped, real_exp))
        btor_hashptr_table_add (sdc->dumped, real_exp);

      /* close s-expression */
      if (real_exp->arity > 0) close_sexp (sdc);

    CLOSE_WRAPPER:
      /* close wrappers */

      /* wrap boolean expressions in bit vector expression */
      if (is_bool && expect_bv && !btor_node_is_bv_const (real_exp))
      {
        fputc (' ', sdc->file);
        bits = btor_bv_one (sdc->btor->mm, 1);
        dump_const_value_aux_smt (sdc, bits);
        btor_bv_free (sdc->btor->mm, bits);
        fputc (' ', sdc->file);
        bits = btor_bv_new (sdc->btor->mm, 1);
        dump_const_value_aux_smt (sdc, bits);
        btor_bv_free (sdc->btor->mm, bits);
        close_sexp (sdc);
      }

      /* close bvnot for non-constants */
      if (btor_node_is_inverted (exp) && !btor_node_is_bv_const (real_exp))
        close_sexp (sdc);

      /* close bool wrapper */
      if (expect_bool && !is_boolean (sdc, real_exp)) close_sexp (sdc);

      /* close zero extend wrapper */
      if (zero_extend) close_sexp (sdc);
    }
  }
  assert (BTOR_EMPTY_STACK (expect_bv_stack));
  BTOR_RELEASE_STACK (args);
  BTOR_RELEASE_STACK (dump);
  BTOR_RELEASE_STACK (expect_bv_stack);
  BTOR_RELEASE_STACK (expect_bool_stack);
  BTOR_RELEASE_STACK (add_space_stack);
  BTOR_RELEASE_STACK (zero_extend_stack);
  BTOR_RELEASE_STACK (depth_stack);
  BTOR_RELEASE_STACK (indices);
  BTOR_RELEASE_STACK (values);
  btor_hashptr_table_delete (visited);
}

static void
dump_let_smt (BtorSMTDumpContext *sdc, BtorNode *exp)
{
  assert (sdc);
  assert (btor_node_is_regular (exp));
  assert (!btor_hashptr_table_get (sdc->dumped, exp));

  bool newline;

  open_sexp (sdc);
  sdc->indent--;
  fputs ("let (", sdc->file);
  fputc ('(', sdc->file);
  dump_smt_id (sdc, exp);  // TODO (ma): better symbol for lets?
  fputc (' ', sdc->file);
  newline      = sdc->newline;
  sdc->newline = false;
  recursively_dump_exp_smt (sdc, exp, !is_boolean (sdc, exp), 0);
  sdc->newline = newline;
  fputs ("))", sdc->file);
  sdc->open_lets++;
  assert (btor_hashptr_table_get (sdc->dumped, exp));
}

static void
collect_shared_exps (BtorSMTDumpContext *sdc,
                     BtorNode *root,
                     BtorNodePtrStack *shared)
{
  uint32_t i, refs;
  BtorNode *cur;
  BtorIntHashTable *cache;
  BtorMemMgr *mm;
  BtorNodePtrStack visit;
  BtorPtrHashBucket *b;

  mm    = sdc->btor->mm;
  cache = btor_hashint_table_new (mm);

  BTOR_INIT_STACK (mm, visit);
  BTOR_INIT_STACK (mm, *shared);
  BTOR_PUSH_STACK (visit, root);

  while (!BTOR_EMPTY_STACK (visit))
  {
    cur = btor_node_real_addr (BTOR_POP_STACK (visit));

    if (btor_hashint_table_contains (cache, cur->id)
        || btor_hashptr_table_get (sdc->dumped, cur)
        || btor_node_is_binder (cur))
      continue;

    b = btor_hashptr_table_get (sdc->dump, cur);
    assert (b);
    refs = b->data.as_int;

    if (!btor_node_is_args (cur)
        && !btor_node_is_param (cur)
        /* constants are always printed */
        && !btor_node_is_bv_const (cur) && refs > 1)
      BTOR_PUSH_STACK (*shared, cur);

    btor_hashint_table_add (cache, cur->id);
    for (i = 0; i < cur->arity; i++) BTOR_PUSH_STACK (visit, cur->e[i]);
  }

  btor_hashint_table_delete (cache);
  BTOR_RELEASE_STACK (visit);
}

static void
recursively_dump_exp_let_smt (BtorSMTDumpContext *sdc,
                              BtorNode *exp,
                              bool expect_bv,
                              uint32_t depth_limit)
{
  uint32_t i;
  BtorNode *cur;
  BtorNodePtrStack shared;

  if (btor_node_is_quantifier (exp))
    recursively_dump_exp_smt (sdc, exp, expect_bv, depth_limit);
  else
  {
    BTOR_INIT_STACK (sdc->btor->mm, shared);
    collect_shared_exps (sdc, exp, &shared);

    if (shared.start)
      qsort (shared.start,
             BTOR_COUNT_STACK (shared),
             sizeof (BtorNode *),
             cmp_node_id);

    for (i = 0; i < BTOR_COUNT_STACK (shared); i++)
    {
      cur = BTOR_PEEK_STACK (shared, i);
      assert (btor_node_is_regular (cur));
      dump_let_smt (sdc, cur);
      fputc (' ', sdc->file);
    }

    recursively_dump_exp_smt (sdc, exp, expect_bv, depth_limit);

    /* close lets */
    for (i = 0; i < BTOR_COUNT_STACK (shared); i++)
    {
      fputc (')', sdc->file);
      //      close_sexp (sdc);
      sdc->open_lets--;
    }

    BTOR_RELEASE_STACK (shared);
  }
}

static void
dump_fun_let_smt2 (BtorSMTDumpContext *sdc, BtorNode *exp)
{
  assert (sdc);
  assert (btor_node_is_regular (exp));
  assert (!btor_hashptr_table_get (sdc->dumped, exp));

  bool is_bool;

  is_bool = is_boolean (sdc, exp);
  open_sexp (sdc);
  fputs ("define-fun ", sdc->file);
  dump_smt_id (sdc, exp);
  fputs (" () ", sdc->file);
  if (is_bool)
    fputs ("Bool", sdc->file);
  else
    btor_dumpsmt_dump_sort_node (exp, sdc->file);
  fputc (' ', sdc->file);
  recursively_dump_exp_smt (sdc, exp, !is_bool, 0);
  close_sexp (sdc);
  fputc ('\n', sdc->file);
  assert (btor_hashptr_table_get (sdc->dumped, exp));
}

static void
dump_fun_smt2 (BtorSMTDumpContext *sdc, BtorNode *fun)
{
  assert (fun);
  assert (sdc);
  assert (btor_node_is_regular (fun));
  assert (btor_node_is_lambda (fun));
  assert (!btor_node_is_array (fun));
  assert (!fun->parameterized);
  assert (!btor_hashptr_table_get (sdc->dumped, fun));

  uint32_t i, refs;
  BtorNode *cur, *param, *fun_body, *p;
  BtorMemMgr *mm = sdc->btor->mm;
  BtorNodePtrStack visit, shared;
  BtorNodeIterator it, iit;
  BtorPtrHashTable *mark;
  BtorPtrHashBucket *b;

  mark = btor_hashptr_table_new (mm,
                                 (BtorHashPtr) btor_node_hash_by_id,
                                 (BtorCmpPtr) btor_node_compare_by_id);
  BTOR_INIT_STACK (mm, visit);
  BTOR_INIT_STACK (mm, shared);

#if 0
  extract_store (sdc, fun, &index, &value, &array);

  if (index)
    {
      assert (value);
      assert (array);
      btor_hashptr_table_add (sdc->stores, fun);
      return;
    }
#endif

  /* collect shared parameterized expressions in function body */
  fun_body = btor_node_binder_get_body (fun);
  BTOR_PUSH_STACK (visit, fun_body);
  while (!BTOR_EMPTY_STACK (visit))
  {
    cur = btor_node_real_addr (BTOR_POP_STACK (visit));

    if (btor_hashptr_table_get (mark, cur)
        || btor_hashptr_table_get (sdc->dumped, cur)
        || (btor_node_is_lambda (cur) && !btor_node_is_array (cur)))
      continue;

    b = btor_hashptr_table_get (sdc->dump, cur);
    assert (b);
    refs = b->data.as_int;

    /* args and params are handled differently */
    /* collect shared parameterized expressions in function body.
     * arguments, parameters, and constants are excluded. */
    if (!btor_node_is_args (cur)
        && !btor_node_is_param (cur)
        /* constants are always printed */
        && !btor_node_is_bv_const (cur) && cur->parameterized && refs > 1)
      BTOR_PUSH_STACK (shared, cur);

    btor_hashptr_table_add (mark, cur);
    for (i = 0; i < cur->arity; i++) BTOR_PUSH_STACK (visit, cur->e[i]);
  }

  /* dump function signature */
  fputs ("(define-fun ", sdc->file);
  dump_smt_id (sdc, fun);
  fputs (" (", sdc->file);

  btor_iter_lambda_init (&it, fun);
  while (btor_iter_lambda_has_next (&it))
  {
    cur   = btor_iter_lambda_next (&it);
    param = cur->e[0];
    if (!btor_hashptr_table_get (mark, cur)) btor_hashptr_table_add (mark, cur);
    if (!btor_hashptr_table_get (mark, param))
      btor_hashptr_table_add (mark, param);
    btor_hashptr_table_add (sdc->dumped, cur);
    btor_hashptr_table_add (sdc->dumped, param);
    if (fun != cur) fputc (' ', sdc->file);
    fputc ('(', sdc->file);
    dump_smt_id (sdc, param);
    fputc (' ', sdc->file);
    btor_dumpsmt_dump_sort_node (param, sdc->file);
    fputc (')', sdc->file);
  }
  fputs (") ", sdc->file);

  if (is_boolean (sdc, fun_body))
    fputs ("Bool", sdc->file);
  else
    btor_dumpsmt_dump_sort_node (fun_body, sdc->file);
  fputc (sdc->pretty_print ? '\n' : ' ', sdc->file);

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
    assert (btor_node_is_regular (cur));
    assert (cur->parameterized);
    dump_let_smt (sdc, cur);
    fputc (' ', sdc->file);
  }
  recursively_dump_exp_smt (sdc, fun_body, !is_boolean (sdc, fun_body), 0);

  /* close lets */
  for (i = 0; i < sdc->open_lets; i++) fputc (')', sdc->file);
  //    close_sexp (sdc);
  sdc->open_lets = 0;

  /* close define-fun */
  fputs (")\n", sdc->file);

  /* due to lambda hashing it is possible that a lambda in 'fun' is shared in
   * different functions. hence, we have to check if all lambda parents of
   * the resp. lambda have already been dumped as otherwise all expressions
   * below have to be removed from 'sdc->dumped' as they will be dumped
   * again in a different function definition. */
  btor_iter_lambda_init (&it, fun);
  while (btor_iter_lambda_has_next (&it))
  {
    cur = btor_iter_lambda_next (&it);
    btor_iter_parent_init (&iit, cur);
    while (btor_iter_parent_has_next (&iit))
    {
      p = btor_iter_parent_next (&iit);
      /* find lambda parent that needs to be dumped but has not yet been
       * dumped */
      if (btor_hashptr_table_get (sdc->dump, p)
          && !btor_hashptr_table_get (sdc->dumped, p)
          && btor_node_is_lambda (p))
      {
        BTOR_PUSH_STACK (visit, cur);
        while (!BTOR_EMPTY_STACK (visit))
        {
          cur = btor_node_real_addr (BTOR_POP_STACK (visit));
          assert (btor_node_is_regular (cur));

          if (!cur->parameterized
              && (!btor_hashptr_table_get (mark, cur)
                  || !btor_hashptr_table_get (sdc->dumped, cur)))
            continue;

          if (btor_hashptr_table_get (sdc->dumped, cur))
            btor_hashptr_table_remove (sdc->dumped, cur, 0, 0);

          for (i = 0; i < cur->arity; i++) BTOR_PUSH_STACK (visit, cur->e[i]);
        }
        break;
      }
    }
  }

  BTOR_RELEASE_STACK (shared);
  BTOR_RELEASE_STACK (visit);
  btor_hashptr_table_delete (mark);
}

static void
dump_declare_fun_smt (BtorSMTDumpContext *sdc, BtorNode *exp)
{
  assert (!btor_hashptr_table_get (sdc->dumped, exp));
  fputs ("(declare-fun ", sdc->file);
  dump_smt_id (sdc, exp);
  fputc (' ', sdc->file);
  if (btor_node_is_bv_var (exp) || btor_node_is_uf_array (exp))
    fputs ("() ", sdc->file);
  btor_dumpsmt_dump_sort_node (exp, sdc->file);
  fputs (")\n", sdc->file);
  btor_hashptr_table_add (sdc->dumped, exp);
}

static void
dump_assert_smt2 (BtorSMTDumpContext *sdc, BtorNode *exp)
{
  assert (sdc);
  assert (exp);
  assert (btor_node_bv_get_width (sdc->btor, exp) == 1);

  open_sexp (sdc);
  fputs ("assert ", sdc->file);
  if (!is_boolean (sdc, exp)) fputs ("(distinct ", sdc->file);
  recursively_dump_exp_smt (sdc, exp, 0, 0);
  if (!is_boolean (sdc, exp)) fputs (" #b0)", sdc->file);
  close_sexp (sdc);
  fputc ('\n', sdc->file);
}

static void
set_logic_smt (BtorSMTDumpContext *sdc, const char *logic)
{
  assert (sdc);

  const char *fmt;

  fmt = "(set-logic %s)\n";
  fprintf (sdc->file, fmt, logic);
}

static uint32_t
get_references (BtorSMTDumpContext *sdc, BtorNode *exp)
{
  assert (exp);

  uint32_t refs = 0;
  BtorNode *cur;
  BtorNodeIterator it;
  BtorPtrHashBucket *b;

  exp = btor_node_real_addr (exp);

  /* get reference count of roots */
  if (btor_hashptr_table_get (sdc->roots, exp)) refs++;
  if (btor_hashptr_table_get (sdc->roots, btor_node_invert (exp))) refs++;

  btor_iter_parent_init (&it, exp);
  while (btor_iter_parent_has_next (&it))
  {
    cur = btor_iter_parent_next (&it);
    assert (btor_node_is_regular (cur));
    b = btor_hashptr_table_get (sdc->dump, cur);
    /* argument nodes are counted differently */
    if (!b || btor_node_is_args (cur)) continue;
    refs++;
  }
  return refs;
}

static bool
has_lambda_parents_only (BtorNode *exp)
{
  BtorNode *p;
  BtorNodeIterator it;
  btor_iter_parent_init (&it, exp);
  while (btor_iter_parent_has_next (&it))
  {
    p = btor_iter_parent_next (&it);
    if (!btor_node_is_lambda (p)) return false;
  }
  return true;
}

static void
mark_boolean (BtorSMTDumpContext *sdc, BtorNodePtrStack *exps)
{
  uint32_t i, j;
  bool is_bool;
  BtorNode *cur;

  /* collect boolean terms */
  for (i = 0; i < BTOR_COUNT_STACK (*exps); i++)
  {
    cur = BTOR_PEEK_STACK (*exps, i);

    /* these nodes are boolean by definition */
    if (btor_node_is_bv_eq (cur) || btor_node_is_fun_eq (cur)
        || btor_node_is_bv_ult (cur)
        || cur == btor_node_real_addr (sdc->btor->true_exp)
        || btor_node_is_quantifier (cur))
    {
      btor_hashptr_table_add (sdc->boolean, cur);
      continue;
    }
    else if (btor_node_is_apply (cur))
    {
      /* boolean function */
      if ((btor_node_is_lambda (cur->e[0])
           && is_boolean (sdc, btor_node_binder_get_body (cur->e[0])))
          || (btor_node_is_fun_cond (cur->e[0]) && is_boolean (sdc, cur->e[1]))
          || (btor_node_is_uf (cur->e[0])
              && btor_sort_is_bool (
                     sdc->btor,
                     btor_sort_fun_get_codomain (
                         sdc->btor, btor_node_get_sort_id (cur->e[0])))))
        btor_hashptr_table_add (sdc->boolean, cur);
      continue;
    }
    else if ((btor_node_is_bv_and (cur) || btor_node_is_bv_cond (cur))
             && btor_node_bv_get_width (sdc->btor, cur) == 1)
    {
      is_bool = true;
      for (j = 0; j < cur->arity; j++)
        if (!(is_bool = is_boolean (sdc, cur->e[j]))) break;

      if (!is_bool) continue;

      btor_hashptr_table_add (sdc->boolean, cur);
    }
  }
}

static void
dump_smt (BtorSMTDumpContext *sdc)
{
  assert (sdc);

  bool quantifiers = false;
  uint32_t i, j;
  BtorNode *e, *cur, *value, *index;
  BtorMemMgr *mm;
  BtorNodePtrStack visit, all, vars, shared, ufs, larr;
  BtorPtrHashBucket *b;
  BtorPtrHashTableIterator it;
  BtorArgsIterator ait;
  BtorPtrHashTable *static_rho;

  mm = sdc->btor->mm;
  BTOR_INIT_STACK (mm, visit);
  BTOR_INIT_STACK (mm, shared);
  BTOR_INIT_STACK (mm, all);
  BTOR_INIT_STACK (mm, vars);
  BTOR_INIT_STACK (mm, ufs);
  BTOR_INIT_STACK (mm, larr);

  btor_iter_hashptr_init (&it, sdc->roots);
  while (btor_iter_hashptr_has_next (&it))
  {
    cur = btor_iter_hashptr_next (&it);
    BTOR_PUSH_STACK (visit, btor_node_real_addr (cur));
  }

  /* collect constants, variables, array variables and functions */
  while (!BTOR_EMPTY_STACK (visit))
  {
    cur = BTOR_POP_STACK (visit);
    assert (btor_node_is_regular (cur));
    assert (!btor_hashptr_table_get (sdc->dumped, cur));

    if (btor_hashptr_table_get (sdc->dump, cur)) continue;

    btor_hashptr_table_add (sdc->dump, cur)->data.as_int = 0;
    BTOR_PUSH_STACK (all, cur);

    if (btor_node_is_bv_var (cur))
      BTOR_PUSH_STACK (vars, cur);
    else if (btor_node_is_uf (cur))
      BTOR_PUSH_STACK (ufs, cur);
    else if (btor_node_is_lambda (cur) && !btor_node_is_array (cur)
             && !cur->parameterized && !has_lambda_parents_only (cur))
      BTOR_PUSH_STACK (shared, cur);
    else if (btor_node_is_lambda (cur) && btor_node_is_array (cur))
      BTOR_PUSH_STACK (larr, cur);
    else if (btor_node_is_quantifier (cur))
      quantifiers = true;

    for (j = 0; j < cur->arity; j++)
      BTOR_PUSH_STACK (visit, btor_node_real_addr (cur->e[j]));
  }

  /* compute reference counts of indices and elements for array writes
   * (represented as lambdas) */
  for (i = 0; i < BTOR_COUNT_STACK (larr); i++)
  {
    cur        = BTOR_PEEK_STACK (larr, i);
    static_rho = btor_node_lambda_get_static_rho (cur);
    assert (static_rho);

    btor_iter_hashptr_init (&it, static_rho);
    while (btor_iter_hashptr_has_next (&it))
    {
      value = btor_node_real_addr (it.bucket->data.as_ptr);
      index = btor_node_real_addr (btor_iter_hashptr_next (&it));
      assert (btor_node_is_args (index));
      assert (btor_node_args_get_arity (sdc->btor, index) == 1);
      if (!(b = btor_hashptr_table_get (sdc->dump, value)))
      {
        b              = btor_hashptr_table_add (sdc->dump, value);
        b->data.as_int = 0;
        BTOR_PUSH_STACK (all, value); /* not yet seen */
      }
      b->data.as_int += 1;
      if (!(b = btor_hashptr_table_get (sdc->dump, index)))
      {
        b              = btor_hashptr_table_add (sdc->dump, index);
        b->data.as_int = 0;
        BTOR_PUSH_STACK (all, index); /* not yet seen */
      }
      b->data.as_int += 1;
    }
  }

  /* compute reference counts of expressions (required for determining shared
   * expressions)*/
  if (all.start)
    qsort (all.start, BTOR_COUNT_STACK (all), sizeof e, cmp_node_id);

  for (i = 0; i < BTOR_COUNT_STACK (all); i++)
  {
    cur = BTOR_PEEK_STACK (all, i);
    b   = btor_hashptr_table_get (sdc->dump, cur);
    assert (b);
    /* cache result for later reuse */
    b->data.as_int += get_references (sdc, cur);

    /* update references for expressions under argument nodes */
    if (btor_node_is_args (cur) && b->data.as_int > 0)
    {
      btor_iter_args_init (&ait, cur);
      while (btor_iter_args_has_next (&ait))
      {
        e = btor_node_real_addr (btor_iter_args_next (&ait));
        assert (btor_hashptr_table_get (sdc->dump, e));
        btor_hashptr_table_get (sdc->dump, e)->data.as_int += b->data.as_int;
      }
    }
  }

  /* collect globally shared expressions */
  for (i = 0; i < BTOR_COUNT_STACK (all); i++)
  {
    cur = BTOR_PEEK_STACK (all, i);
    b   = btor_hashptr_table_get (sdc->dump, cur);
    assert (b);

    if (b->data.as_int <= 1
        /* parameterized expressions are only shared within a function */
        || cur->parameterized
        || btor_node_is_param (cur)
        /* constants are always printed */
        || btor_node_is_bv_const (cur)
        /* for variables and functions the resp. symbols are always printed */
        || btor_node_is_bv_var (cur)
        || (btor_node_is_lambda (cur) && !btor_node_is_array (cur))
        || btor_node_is_uf (cur)
        /* argument nodes are never printed */
        || btor_node_is_args (cur))
      continue;

    BTOR_PUSH_STACK (shared, cur);
  }

  /* collect boolean terms */
  mark_boolean (sdc, &all);

  /* begin dump */
  if (quantifiers)
  {
    if (BTOR_EMPTY_STACK (ufs))
      set_logic_smt (sdc, "BV");
    else
      set_logic_smt (sdc, "UFBV");
  }
  else
  {
    if (BTOR_EMPTY_STACK (ufs))
      set_logic_smt (sdc, "QF_BV");
    else
      set_logic_smt (sdc, "QF_UFBV");
  }

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

  /* dump shared expressions and functions */
  if (shared.start)
    qsort (shared.start, BTOR_COUNT_STACK (shared), sizeof e, cmp_node_id);

  for (i = 0; i < BTOR_COUNT_STACK (shared); i++)
  {
    cur = BTOR_PEEK_STACK (shared, i);
    assert (btor_node_is_regular (cur));

    if (btor_hashptr_table_get (sdc->dumped, cur)) continue;

    assert (!cur->parameterized);

    if (btor_node_is_lambda (cur) && !btor_node_is_array (cur))
      dump_fun_smt2 (sdc, cur);
    else
      dump_fun_let_smt2 (sdc, cur);
  }

  /* dump assertions/build root */
  btor_iter_hashptr_init (&it, sdc->roots);
  while (btor_iter_hashptr_has_next (&it))
  {
    cur = btor_iter_hashptr_next (&it);
    dump_assert_smt2 (sdc, cur);
  }
  assert (sdc->open_lets == 0);

#ifndef NDEBUG
  btor_iter_hashptr_init (&it, sdc->dump);
  while (btor_iter_hashptr_has_next (&it))
  {
    cur = btor_iter_hashptr_next (&it);
    /* constants and function applications are always dumped (hence, not in
     * mark) */
    if (btor_node_is_bv_const (cur)
        || btor_node_is_apply (cur)
        /* argument nodes are never dumped and not in mark */
        || btor_node_is_args (cur) || cur->parameterized
        || (btor_node_is_lambda (cur) && btor_node_is_array (cur)))
      continue;
    assert (btor_hashptr_table_get (sdc->dumped, cur));
  }
#endif

  BTOR_RELEASE_STACK (shared);
  BTOR_RELEASE_STACK (visit);
  BTOR_RELEASE_STACK (all);
  BTOR_RELEASE_STACK (vars);
  BTOR_RELEASE_STACK (ufs);
  BTOR_RELEASE_STACK (larr);

  fputs ("(check-sat)\n", sdc->file);
  fputs ("(exit)\n", sdc->file);
  fflush (sdc->file);
}

static void
dump_smt_aux (Btor *btor, FILE *file, BtorNode **roots, uint32_t nroots)
{
  assert (btor);
  assert (file);

  uint32_t i;
  BtorNode *tmp, *tmp_roots[nroots];
  BtorPtrHashTableIterator it;
  BtorSMTDumpContext *sdc;

  for (i = 0; i < nroots; i++) tmp_roots[i] = roots[i];

  sdc = new_smt_dump_context (btor, file);

  if (nroots)
  {
    for (i = 0; i < nroots; i++)
      add_root_to_smt_dump_context (sdc, tmp_roots[i]);
  }
  else
  {
    if (btor->inconsistent)
    {
      tmp = btor_exp_false (btor);
      add_root_to_smt_dump_context (sdc, tmp);
      btor_node_release (btor, tmp);
    }
    else if (btor->unsynthesized_constraints->count == 0
             && btor->synthesized_constraints->count == 0
             && btor->embedded_constraints->count == 0)
    {
      tmp = btor_exp_true (btor);
      add_root_to_smt_dump_context (sdc, tmp);
      btor_node_release (btor, tmp);
    }
    else
    {
      btor_iter_hashptr_init (&it, btor->unsynthesized_constraints);
      btor_iter_hashptr_queue (&it, btor->synthesized_constraints);
      btor_iter_hashptr_queue (&it, btor->embedded_constraints);
      while (btor_iter_hashptr_has_next (&it))
        add_root_to_smt_dump_context (sdc, btor_iter_hashptr_next (&it));
    }
  }

  dump_smt (sdc);
  delete_smt_dump_context (sdc);
}

void
btor_dumpsmt_dump (Btor *btor, FILE *file)
{
  assert (btor);
  assert (file);
  dump_smt_aux (btor, file, 0, 0);
}

void
btor_dumpsmt_dump_node (Btor *btor, FILE *file, BtorNode *exp, uint32_t depth)
{
  assert (btor);

  uint32_t i;
  BtorNode *cur, *real_exp, *binder;
  BtorSMTDumpContext *sdc;
  BtorNodePtrStack visit, all;
  BtorArgsIterator ait;
  BtorPtrHashBucket *b;

  real_exp = btor_node_real_addr (exp);

  BTOR_INIT_STACK (btor->mm, all);
  BTOR_INIT_STACK (btor->mm, visit);
  sdc          = new_smt_dump_context (btor, file);
  sdc->newline = false;

  if (!exp)
  {
    fprintf (file, "null\n");
    goto CLEANUP;
  }
  else if (btor_node_is_args (real_exp))
  {
    fprintf (file, "%s_%d\n", g_kind2smt[real_exp->kind], real_exp->id);
    goto CLEANUP;
  }
  else if (btor_node_is_bv_var (exp) || btor_node_is_uf (exp))
  {
    dump_declare_fun_smt (sdc, exp);
    goto CLEANUP;
  }

  BTOR_PUSH_STACK (visit, exp);
  while (!BTOR_EMPTY_STACK (visit))
  {
    cur = btor_node_real_addr (BTOR_POP_STACK (visit));

    if (btor_hashptr_table_get (sdc->dump, cur)) continue;

    if (btor_node_is_bv_var (cur) || btor_node_is_uf (cur)
        || (btor_node_is_param (cur)
            && (!(binder = btor_node_param_get_binder (cur))
                || !btor_hashptr_table_get (sdc->dump, binder))))
      btor_hashptr_table_add (sdc->dumped, cur);

    btor_hashptr_table_add (sdc->dump, cur);
    BTOR_PUSH_STACK (all, cur);

    for (i = 0; i < cur->arity; i++) BTOR_PUSH_STACK (visit, cur->e[i]);
  }

  /* compute reference counts of expressions (required for determining shared
   * expressions)*/
  if (all.start)
    qsort (all.start, BTOR_COUNT_STACK (all), sizeof (BtorNode *), cmp_node_id);

  for (i = 0; i < BTOR_COUNT_STACK (all); i++)
  {
    cur = BTOR_PEEK_STACK (all, i);
    b   = btor_hashptr_table_get (sdc->dump, cur);
    assert (b);
    assert (b->data.as_int == 0);
    /* cache result for later reuse */
    b->data.as_int = get_references (sdc, cur);

    /* update references for expressions under argument nodes */
    if (btor_node_is_args (cur) && b->data.as_int > 0)
    {
      btor_iter_args_init (&ait, cur);
      while (btor_iter_args_has_next (&ait))
      {
        cur = btor_node_real_addr (btor_iter_args_next (&ait));
        assert (btor_hashptr_table_get (sdc->dump, cur));
        btor_hashptr_table_get (sdc->dump, cur)->data.as_int += b->data.as_int;
      }
    }
  }

  mark_boolean (sdc, &all);
  if (btor_node_is_lambda (exp) && !btor_node_is_array (exp))
    dump_fun_smt2 (sdc, exp);
  else
  {
    recursively_dump_exp_let_smt (sdc, exp, false, depth);
  }
CLEANUP:
  delete_smt_dump_context (sdc);
  BTOR_RELEASE_STACK (all);
  BTOR_RELEASE_STACK (visit);
}
