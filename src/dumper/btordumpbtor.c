/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2014 Armin Biere.
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2012-2017 Aina Niemetz.
 *  Copyright (C) 2012-2016 Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btordumpbtor.h"
#include "btorbv.h"
#include "btorcore.h"
#include "btorexp.h"
#include "btornode.h"
#include "btoropt.h"
#include "btorsort.h"
#include "utils/btorhashptr.h"
#include "utils/btormem.h"
#include "utils/btornodeiter.h"
#include "utils/btorstack.h"

typedef struct BtorDumpContextLatch BtorDumpContextLatch;

struct BtorDumpContextLatch
{
  BtorNode *latch;
  BtorNode *init;
  BtorNode *next;
};

struct BtorDumpContext
{
  int maxid;
  int maxsortid;
  int version;
  Btor *btor;
  BtorPtrHashTable *idtab;
  BtorPtrHashTable *inputs;
  BtorPtrHashTable *latches;
  BtorPtrHashTable *sorts;
  BtorNodePtrStack outputs;
  BtorNodePtrStack bads;
  BtorNodePtrStack constraints;
  BtorNodePtrStack roots;
  BtorNodePtrStack work;
  BtorPtrHashTable *no_dump;
};

BtorDumpContext *
btor_dumpbtor_new_dump_context (Btor *btor)
{
  BtorDumpContext *res;
  BTOR_CNEW (btor->mm, res);
  res->btor    = btor;
  res->version = 1;
  res->inputs  = btor_hashptr_table_new (btor->mm,
                                        (BtorHashPtr) btor_hash_exp_by_id,
                                        (BtorCmpPtr) btor_compare_exp_by_id);
  res->latches = btor_hashptr_table_new (btor->mm,
                                         (BtorHashPtr) btor_hash_exp_by_id,
                                         (BtorCmpPtr) btor_compare_exp_by_id);
  res->idtab   = btor_hashptr_table_new (btor->mm,
                                       (BtorHashPtr) btor_hash_exp_by_id,
                                       (BtorCmpPtr) btor_compare_exp_by_id);
  res->sorts   = btor_hashptr_table_new (btor->mm, 0, 0);
  res->no_dump = btor_hashptr_table_new (btor->mm, 0, 0);

  /* set start id for roots */
  if (!btor_opt_get (btor, BTOR_OPT_PRETTY_PRINT))
    res->maxid = BTOR_COUNT_STACK (btor->nodes_id_table);

  BTOR_INIT_STACK (btor->mm, res->outputs);
  BTOR_INIT_STACK (btor->mm, res->bads);
  BTOR_INIT_STACK (btor->mm, res->constraints);
  BTOR_INIT_STACK (btor->mm, res->roots);
  BTOR_INIT_STACK (btor->mm, res->work);

  return res;
}

void
btor_dumpbtor_delete_dump_context (BtorDumpContext *bdc)
{
  BtorPtrHashTableIterator it;

  BTOR_RELEASE_STACK (bdc->work);

  while (!BTOR_EMPTY_STACK (bdc->roots))
    btor_release_exp (bdc->btor, BTOR_POP_STACK (bdc->roots));
  BTOR_RELEASE_STACK (bdc->roots);

  while (!BTOR_EMPTY_STACK (bdc->outputs))
    btor_release_exp (bdc->btor, BTOR_POP_STACK (bdc->outputs));
  BTOR_RELEASE_STACK (bdc->outputs);

  while (!BTOR_EMPTY_STACK (bdc->bads))
    btor_release_exp (bdc->btor, BTOR_POP_STACK (bdc->bads));
  BTOR_RELEASE_STACK (bdc->bads);

  while (!BTOR_EMPTY_STACK (bdc->constraints))
    btor_release_exp (bdc->btor, BTOR_POP_STACK (bdc->constraints));
  BTOR_RELEASE_STACK (bdc->constraints);

  btor_iter_hashptr_init (&it, bdc->inputs);
  while (btor_iter_hashptr_has_next (&it))
    btor_release_exp (bdc->btor, btor_iter_hashptr_next (&it));
  btor_hashptr_table_delete (bdc->inputs);

  btor_iter_hashptr_init (&it, bdc->latches);
  while (btor_iter_hashptr_has_next (&it))
  {
    BtorDumpContextLatch *l = it.bucket->data.as_ptr;
    btor_release_exp (bdc->btor, l->latch);
    if (l->next) btor_release_exp (bdc->btor, l->next);
    if (l->init) btor_release_exp (bdc->btor, l->init);
    BTOR_DELETE (bdc->btor->mm, l);
    (void) btor_iter_hashptr_next (&it);
  }
  btor_hashptr_table_delete (bdc->latches);

  btor_iter_hashptr_init (&it, bdc->idtab);
  while (btor_iter_hashptr_has_next (&it))
    btor_release_exp (bdc->btor, btor_iter_hashptr_next (&it));
  btor_hashptr_table_delete (bdc->idtab);

  btor_hashptr_table_delete (bdc->sorts);
  btor_hashptr_table_delete (bdc->no_dump);
  BTOR_DELETE (bdc->btor->mm, bdc);
}

void
btor_dumpbtor_add_input_to_dump_context (BtorDumpContext *bdc, BtorNode *input)
{
  assert (BTOR_IS_REGULAR_NODE (input));
  assert (btor_is_bv_var_node (input));
  assert (!btor_hashptr_table_get (bdc->inputs, input));
  assert (!btor_hashptr_table_get (bdc->latches, input));
  (void) btor_copy_exp (bdc->btor, input);
  (void) btor_hashptr_table_add (bdc->inputs, input);
}

void
btor_dumpbtor_add_latch_to_dump_context (BtorDumpContext *bdc, BtorNode *latch)
{
  BtorPtrHashBucket *b;
  BtorDumpContextLatch *bdcl;
  assert (BTOR_IS_REGULAR_NODE (latch));
  assert (btor_is_bv_var_node (latch));
  assert (!btor_hashptr_table_get (bdc->inputs, latch));
  assert (!btor_hashptr_table_get (bdc->latches, latch));
  b = btor_hashptr_table_add (bdc->latches, latch);
  BTOR_CNEW (bdc->btor->mm, bdcl);
  bdcl->latch    = btor_copy_exp (bdc->btor, latch);
  b->data.as_ptr = bdcl;
}

void
btor_dumpbtor_add_next_to_dump_context (BtorDumpContext *bdc,
                                        BtorNode *latch,
                                        BtorNode *next)
{
  BtorDumpContextLatch *l;
  BtorPtrHashBucket *b;
  b = btor_hashptr_table_get (bdc->latches, latch);
  assert (b);
  l = b->data.as_ptr;
  assert (l);
  assert (l->latch == latch);
  assert (!l->next);
  l->next = btor_copy_exp (bdc->btor, next);
}

void
btor_dumpbtor_add_init_to_dump_context (BtorDumpContext *bdc,
                                        BtorNode *latch,
                                        BtorNode *init)
{
  BtorDumpContextLatch *l;
  BtorPtrHashBucket *b;
  b = btor_hashptr_table_get (bdc->latches, latch);
  assert (b);
  l = b->data.as_ptr;
  assert (l);
  assert (l->latch == latch);
  assert (!l->init);
  l->init = btor_copy_exp (bdc->btor, init);
}

void
btor_dumpbtor_add_bad_to_dump_context (BtorDumpContext *bdc, BtorNode *bad)
{
  (void) btor_copy_exp (bdc->btor, bad);
  BTOR_PUSH_STACK (bdc->bads, bad);
}

void
btor_dumpbtor_add_output_to_dump_context (BtorDumpContext *bdc,
                                          BtorNode *output)
{
  (void) btor_copy_exp (bdc->btor, output);
  BTOR_PUSH_STACK (bdc->outputs, output);
}

void
btor_dumpbtor_add_root_to_dump_context (BtorDumpContext *bdc, BtorNode *root)
{
  (void) btor_copy_exp (bdc->btor, root);
  BTOR_PUSH_STACK (bdc->roots, root);
}

void
btor_dumpbtor_add_constraint_to_dump_context (BtorDumpContext *bdc,
                                              BtorNode *constraint)
{
  (void) btor_copy_exp (bdc->btor, constraint);
  BTOR_PUSH_STACK (bdc->constraints, constraint);
}

static int
bdcid (BtorDumpContext *bdc, BtorNode *node)
{
  BtorPtrHashBucket *b;
  BtorNode *real;
  int res;
  real = BTOR_REAL_ADDR_NODE (node);
  b    = btor_hashptr_table_get (bdc->idtab, real);
  if (!b)
  {
    b = btor_hashptr_table_add (bdc->idtab, btor_copy_exp (bdc->btor, node));
    if (btor_opt_get (bdc->btor, BTOR_OPT_PRETTY_PRINT))
      b->data.as_int = ++bdc->maxid;
    else
      b->data.as_int = real->id;
  }
  res = b->data.as_int;
  if (!BTOR_IS_REGULAR_NODE (node)) res = -res;
  return res;
}

static int
bdcsortid (BtorDumpContext *bdc, BtorSort *sort)
{
  assert (btor_hashptr_table_get (bdc->sorts, sort));
  return btor_hashptr_table_get (bdc->sorts, sort)->data.as_int;
}

static int
compare_sorts (const void *p1, const void *p2)
{
  BtorSort *a, *b;
  a = *((BtorSort **) p1);
  b = *((BtorSort **) p2);
  return a->id - b->id;
}

static BtorSort *
get_sort (BtorDumpContext *bdc, BtorNode *node)
{
  BtorSort *sort;
  sort = btor_sort_get_by_id (bdc->btor, btor_exp_get_sort_id (node));
  assert (btor_hashptr_table_get (bdc->sorts, sort));
  assert (sort->refs > 1);
  return sort;
}

#ifndef NDEBUG
static bool
has_lambda_parent (BtorNode *exp)
{
  BtorNode *p;
  BtorNodeIterator it;
  btor_iter_parent_init (&it, exp);
  while (btor_iter_parent_has_next (&it))
  {
    p = btor_iter_parent_next (&it);
    if (btor_is_lambda_node (p)) return true;
  }
  return false;
}
#endif

static void
mark_no_dump (BtorDumpContext *bdc, BtorNode *node)
{
  uint32_t i;
  BtorNode *cur;
  BtorNodePtrStack visit;
  BtorMemMgr *mm;

  mm = bdc->btor->mm;
  BTOR_INIT_STACK (mm, visit);
  BTOR_PUSH_STACK (visit, node);
  while (!BTOR_EMPTY_STACK (visit))
  {
    cur = BTOR_REAL_ADDR_NODE (BTOR_POP_STACK (visit));

    if (!cur->parameterized || btor_hashptr_table_get (bdc->no_dump, cur))
      continue;

    btor_hashptr_table_add (bdc->no_dump, cur);
    for (i = 0; i < cur->arity; i++) BTOR_PUSH_STACK (visit, cur->e[i]);
  }
  BTOR_RELEASE_STACK (visit);
}

static void
bdcnode (BtorDumpContext *bdc, BtorNode *node, FILE *file)
{
  int i;
  char *symbol, *cbits;
  const char *op;
  uint32_t opt;
  BtorNode *n, *index, *value;
  BtorArgsIterator ait;
  BtorNodeIterator nit;
  BtorPtrHashTable *rho;
  BtorBitVector *bits;

  node  = BTOR_REAL_ADDR_NODE (node);
  cbits = 0;

  /* argument nodes will not be dumped as they are purely internal nodes */
  if (btor_is_args_node (node)) return;

#if 0
  if (bdc->version == 2
      && (btor_is_args_node (node)
	  || (!BTOR_IS_FIRST_CURRIED_LAMBDA (node)
	      && BTOR_IS_CURRIED_LAMBDA_NODE (node))))
    return;
#endif

  /* do not dump parameterized nodes that belong to a "write-lambda" */
  if (btor_hashptr_table_get (bdc->no_dump, node)) return;

  switch (node->kind)
  {
    case BTOR_ADD_NODE: op = "add"; break;
    case BTOR_AND_NODE: op = "and"; break;
    case BTOR_CONCAT_NODE: op = "concat"; break;
    case BTOR_COND_NODE: op = bdc->version == 1 ? "cond" : "ite"; break;
    case BTOR_BV_EQ_NODE:
    case BTOR_FUN_EQ_NODE: op = "eq"; break;
    case BTOR_MUL_NODE: op = "mul"; break;
    case BTOR_PROXY_NODE: op = "proxy"; break;
    case BTOR_SLL_NODE: op = "sll"; break;
    case BTOR_SRL_NODE: op = "srl"; break;
    case BTOR_UDIV_NODE: op = "udiv"; break;
    case BTOR_ULT_NODE: op = "ult"; break;
    case BTOR_UREM_NODE: op = "urem"; break;
    case BTOR_SLICE_NODE: op = "slice"; break;
    case BTOR_UF_NODE:
      op = btor_is_uf_array_node (node) ? "array" : "uf";
      break;
    case BTOR_BV_CONST_NODE:
      bits = btor_const_get_bits (node);
      opt  = btor_opt_get (bdc->btor, BTOR_OPT_OUTPUT_NUMBER_FORMAT);
      if (btor_bv_is_zero (bits))
      {
        op = "zero";
      }
      else if (btor_bv_is_one (bits))
      {
        op = "one";
      }
      else if (btor_bv_is_ones (bits))
      {
        op = "ones";
      }
      else if (opt == BTOR_OUTPUT_BASE_HEX)
      {
        op    = "consth";
        cbits = btor_bv_to_hex_char (bdc->btor->mm, bits);
      }
      else if (opt == BTOR_OUTPUT_BASE_DEC
               || btor_bv_small_positive_int (bits) > 0)
      {
        op    = "constd";
        cbits = btor_bv_to_dec_char (bdc->btor->mm, bits);
      }
      else
      {
        op    = "const";
        cbits = btor_bv_to_char (bdc->btor->mm, bits);
      }
      break;
    case BTOR_PARAM_NODE: op = "param"; break;
    case BTOR_LAMBDA_NODE:
      if (btor_opt_get (bdc->btor, BTOR_OPT_REWRITE_LEVEL) == 0
          && btor_lambda_get_static_rho (node))
      {
        op = "write";
        mark_no_dump (bdc, node->e[1]);
      }
      else if (bdc->version == 1 || btor_get_fun_arity (bdc->btor, node) == 1)
        op = "lambda";
      else
        op = "fun";
      break;
    case BTOR_APPLY_NODE:
      if (btor_is_uf_array_node (node->e[0])
          || (btor_opt_get (bdc->btor, BTOR_OPT_REWRITE_LEVEL) == 0
              && btor_is_lambda_node (node->e[0])
              && btor_lambda_get_static_rho (node->e[0])))
        op = "read";
      else
        op = "apply";
      break;
    case BTOR_ARGS_NODE: op = "args"; break;
    default: assert (node->kind == BTOR_BV_VAR_NODE); op = "var";
  }

  /* print id, operator and sort */
  if (bdc->version == 1)
  {
    fprintf (file, "%d %s", bdcid (bdc, node), op);

    /* print index bit width of arrays */
    if (btor_is_uf_array_node (node) || btor_is_fun_cond_node (node))
    {
      fprintf (file, " %d", btor_get_fun_exp_width (bdc->btor, node));
      fprintf (file, " %d", btor_get_index_exp_width (bdc->btor, node));
    }
    else if (btor_is_lambda_node (node))
    {
      fprintf (file, " %d", btor_get_fun_exp_width (bdc->btor, node));
      fprintf (file, " %d", btor_get_exp_width (bdc->btor, node->e[0]));
    }
    else if (!btor_is_uf_node (node))
      fprintf (file, " %d", btor_get_exp_width (bdc->btor, node));

    if (btor_is_apply_node (node))
    {
      fprintf (file, " %d", bdcid (bdc, node->e[0]));
      btor_iter_args_init (&ait, node->e[1]);
      while (btor_iter_args_has_next (&ait))
        fprintf (file, " %d", bdcid (bdc, btor_iter_args_next (&ait)));
      goto DONE;
    }
  }
  else
  {
    fprintf (file,
             "%d %s %d",
             bdcid (bdc, node),
             op,
             bdcsortid (bdc, get_sort (bdc, node)));

    if (btor_is_apply_node (node))
    {
      fprintf (file, " %d", bdcid (bdc, node->e[0]));
      btor_iter_args_init (&ait, node->e[1]);
      while (btor_iter_args_has_next (&ait))
        fprintf (file, " %d", bdcid (bdc, btor_iter_args_next (&ait)));
      goto DONE;
    }
    else if (strcmp (op, "fun") == 0)
    {
      assert (!has_lambda_parent (node));
      btor_iter_lambda_init (&nit, node);
      while (btor_iter_lambda_has_next (&nit))
      {
        n = btor_iter_lambda_next (&nit);
        fprintf (file, " %d", bdcid (bdc, n->e[0]));
      }
      fprintf (file, " %d", bdcid (bdc, btor_lambda_get_body (node)));
      goto DONE;
    }
  }

  /* print children or const values */
  if (cbits)
  {
    fprintf (file, " %s", cbits);
    btor_mem_freestr (bdc->btor->mm, cbits);
  }
  else if (btor_is_proxy_node (node))
    fprintf (file, " %d", bdcid (bdc, node->simplified));
  /* print write instead of lambda */
  else if (btor_opt_get (bdc->btor, BTOR_OPT_REWRITE_LEVEL) == 0
           && btor_is_lambda_node (node) && btor_lambda_get_static_rho (node))
  {
    assert (btor_get_fun_arity (bdc->btor, node) == 1);
    rho = btor_lambda_get_static_rho (node);
    assert (rho->count == 1);
    index = rho->first->key;
    value = rho->first->data.as_ptr;
    assert (value);
    assert (BTOR_IS_REGULAR_NODE (index));
    assert (btor_is_args_node (index));
    assert (BTOR_IS_REGULAR_NODE (node->e[1]));
    assert (btor_is_bv_cond_node (node->e[1]));
    assert (BTOR_IS_REGULAR_NODE (node->e[1]->e[2]));
    assert (btor_is_apply_node (node->e[1]->e[2]));
    fprintf (file,
             " %d %d %d",
             bdcid (bdc, node->e[1]->e[2]->e[0]),
             bdcid (bdc, index->e[0]),
             bdcid (bdc, value));
  }
  else
    for (i = 0; i < node->arity; i++)
      fprintf (file, " %d", bdcid (bdc, node->e[i]));

  /* print slice limits/var symbols */
  if (node->kind == BTOR_SLICE_NODE)
    fprintf (file,
             " %d %d",
             btor_slice_get_upper (node),
             btor_slice_get_lower (node));
  else if (btor_is_bv_var_node (node) || btor_is_uf_node (node))
  {
    symbol = btor_get_symbol_exp (bdc->btor, node);
    if (symbol) fprintf (file, " %s", symbol);
  }
DONE:
  fputc ('\n', file);
}

static void
bdcsort (BtorDumpContext *bdc, BtorSort *sort, FILE *file)
{
  unsigned i, id;
  const char *kind;

  /* already dumped */
  if (btor_hashptr_table_get (bdc->sorts, sort)) return;

  switch (sort->kind)
  {
    default:
    case BTOR_BOOL_SORT: kind = "bool"; break;
    case BTOR_BITVEC_SORT: kind = "bv"; break;
    case BTOR_ARRAY_SORT: kind = "array"; break;
    case BTOR_FUN_SORT: kind = "fun"; break;
  }

  id = sort->id;
  if (btor_opt_get (bdc->btor, BTOR_OPT_PRETTY_PRINT)) id = ++bdc->maxsortid;

  fprintf (file, "%d sort %s", id, kind);

  if (sort->kind == BTOR_BITVEC_SORT)
    fprintf (file, " %d", sort->bitvec.width);
  else if (sort->kind == BTOR_ARRAY_SORT)
    fprintf (file,
             " %d %d",
             bdcsortid (bdc, sort->array.index),
             bdcsortid (bdc, sort->array.element));
  else if (sort->kind == BTOR_FUN_SORT)
  {
    if (sort->fun.arity == 1)
      fprintf (file, " %d", bdcsortid (bdc, sort->fun.domain));
    else
    {
      for (i = 0; i < sort->fun.arity; i++)
        fprintf (
            file, " %d", bdcsortid (bdc, sort->fun.domain->tuple.elements[i]));
    }
    fprintf (file, " %d", bdcsortid (bdc, sort->fun.codomain));
  }
  fputc ('\n', file);

  btor_hashptr_table_add (bdc->sorts, sort)->data.as_int = id;
}

static void
bdcsorts (BtorDumpContext *bdc, BtorNode *start, FILE *file)
{
  int i;
  BtorMemMgr *mm;
  BtorNodePtrStack work;
  BtorSortPtrStack sorts;
  BtorNode *cur;
  BtorSort *sort;
  BtorPtrHashTable *mark_nodes, *mark_sorts;

  mm         = bdc->btor->mm;
  mark_nodes = btor_hashptr_table_new (mm,
                                       (BtorHashPtr) btor_hash_exp_by_id,
                                       (BtorCmpPtr) btor_compare_exp_by_id);
  mark_sorts = btor_hashptr_table_new (mm, 0, 0);

  BTOR_INIT_STACK (mm, sorts);
  BTOR_INIT_STACK (mm, work);
  BTOR_PUSH_STACK (work, start);

  while (!BTOR_EMPTY_STACK (work))
  {
    cur = BTOR_REAL_ADDR_NODE (BTOR_POP_STACK (work));

    if (btor_hashptr_table_get (mark_nodes, cur)) continue;

    (void) btor_hashptr_table_add (mark_nodes, cur);

    sort = btor_sort_get_by_id (bdc->btor, btor_exp_get_sort_id (cur));

    if (!(btor_hashptr_table_get (bdc->sorts, sort)
          || btor_hashptr_table_get (mark_sorts, sort)))
    {
      (void) btor_hashptr_table_add (mark_sorts, sort);
      BTOR_PUSH_STACK (sorts, sort);
    }

    for (i = 0; i < cur->arity; i++) BTOR_PUSH_STACK (work, cur->e[i]);
  }

  qsort (sorts.start,
         BTOR_COUNT_STACK (sorts),
         sizeof (BtorSort *),
         compare_sorts);

  for (i = 0; i < BTOR_COUNT_STACK (sorts); i++)
  {
    sort = BTOR_PEEK_STACK (sorts, i);
    bdcsort (bdc, sort, file);
  }

  btor_hashptr_table_delete (mark_nodes);
  btor_hashptr_table_delete (mark_sorts);
  BTOR_RELEASE_STACK (sorts);
  BTOR_RELEASE_STACK (work);
}

static void
bdcrec (BtorDumpContext *bdc, BtorNode *start, FILE *file)
{
  BtorNode *node;
  int i;

  if (bdc->version == 2) bdcsorts (bdc, start, file);

  assert (BTOR_EMPTY_STACK (bdc->work));

  BTOR_PUSH_STACK (bdc->work, start);
  while (!BTOR_EMPTY_STACK (bdc->work))
  {
    node = BTOR_POP_STACK (bdc->work);
    if (node)
    {
      node = BTOR_REAL_ADDR_NODE (node);
      if (btor_hashptr_table_get (bdc->idtab, node)) continue;
      BTOR_PUSH_STACK (bdc->work, node);
      BTOR_PUSH_STACK (bdc->work, 0);

      for (i = node->arity - 1; i >= 0; i--)
        BTOR_PUSH_STACK (bdc->work, node->e[i]);

      if (node->simplified) BTOR_PUSH_STACK (bdc->work, node->simplified);
    }
    else
    {
      assert (!BTOR_EMPTY_STACK (bdc->work));
      node = BTOR_POP_STACK (bdc->work);
      assert (BTOR_IS_REGULAR_NODE (node));
      (void) bdcid (bdc, node);
      bdcnode (bdc, node, file);
    }
  }
}

void
btor_dumpbtor_dump_bdc (BtorDumpContext *bdc, FILE *file)
{
  BtorPtrHashTableIterator it;
  int i;
  char *symbol;

  btor_iter_hashptr_init (&it, bdc->inputs);
  while (btor_iter_hashptr_has_next (&it))
  {
    BtorNode *node = btor_iter_hashptr_next (&it);
    int id;
    assert (node);
    assert (BTOR_IS_REGULAR_NODE (node));
    assert (btor_is_bv_var_node (node));
    id = bdcid (bdc, node);
    fprintf (file, "%d input %d", id, btor_get_exp_width (bdc->btor, node));
    if ((symbol = btor_get_symbol_exp (bdc->btor, node)))
      fprintf (file, " %s", symbol);
    fputc ('\n', file);
  }

  btor_iter_hashptr_init (&it, bdc->latches);
  while (btor_iter_hashptr_has_next (&it))
  {
    BtorNode *node = btor_iter_hashptr_next (&it);
    int id;
    assert (node);
    assert (BTOR_IS_REGULAR_NODE (node));
    assert (btor_is_bv_var_node (node));
    id = bdcid (bdc, node);
    fprintf (file, "%d latch %d", id, btor_get_exp_width (bdc->btor, node));
    if ((symbol = btor_get_symbol_exp (bdc->btor, node)))
      fprintf (file, " %s", symbol);
    fputc ('\n', file);
  }

  btor_iter_hashptr_init (&it, bdc->latches);
  while (btor_iter_hashptr_has_next (&it))
  {
    BtorDumpContextLatch *bdcl = it.bucket->data.as_ptr;
    int id;
    assert (bdcl->latch);
    assert (BTOR_IS_REGULAR_NODE (bdcl->latch));
    assert (btor_is_bv_var_node (bdcl->latch));
    if (bdcl->next)
    {
      bdcrec (bdc, bdcl->next, file);
      id = ++bdc->maxid;
      fprintf (file,
               "%d next %d %d %d\n",
               id,
               btor_get_exp_width (bdc->btor, bdcl->next),
               bdcid (bdc, bdcl->latch),
               bdcid (bdc, bdcl->next));
    }
    if (bdcl->init)
    {
      bdcrec (bdc, bdcl->init, file);
      id = ++bdc->maxid;
      fprintf (file,
               "%d init %d %d %d\n",
               id,
               btor_get_exp_width (bdc->btor, bdcl->init),
               bdcid (bdc, bdcl->latch),
               bdcid (bdc, bdcl->init));
    }
    (void) btor_iter_hashptr_next (&it);
  }

  for (i = 0; i < BTOR_COUNT_STACK (bdc->outputs); i++)
  {
    BtorNode *node = BTOR_PEEK_STACK (bdc->outputs, i);
    int id;
    bdcrec (bdc, node, file);
    id = ++bdc->maxid;
    fprintf (file,
             "%d output %d %d\n",
             id,
             btor_get_exp_width (bdc->btor, node),
             bdcid (bdc, node));
  }

  for (i = 0; i < BTOR_COUNT_STACK (bdc->bads); i++)
  {
    BtorNode *node = BTOR_PEEK_STACK (bdc->bads, i);
    int id;
    bdcrec (bdc, node, file);
    id = ++bdc->maxid;
    fprintf (file,
             "%d bad %d %d\n",
             id,
             btor_get_exp_width (bdc->btor, node),
             bdcid (bdc, node));
  }

  for (i = 0; i < BTOR_COUNT_STACK (bdc->constraints); i++)
  {
    BtorNode *node = BTOR_PEEK_STACK (bdc->constraints, i);
    int id;
    bdcrec (bdc, node, file);
    id = ++bdc->maxid;
    fprintf (file,
             "%d constraint %d %d\n",
             id,
             btor_get_exp_width (bdc->btor, node),
             bdcid (bdc, node));
  }

  for (i = 0; i < BTOR_COUNT_STACK (bdc->roots); i++)
  {
    BtorNode *node = BTOR_PEEK_STACK (bdc->roots, i);
    int id, len;
    bdcrec (bdc, node, file);
    id = ++bdc->maxid;
    if (bdc->version == 1)
    {
      if (btor_sort_is_fun (bdc->btor, btor_exp_get_sort_id (node)))
        len = btor_get_fun_exp_width (bdc->btor, node);
      else
        len = btor_get_exp_width (bdc->btor, node);
      fprintf (file, "%d root %d %d\n", id, len, bdcid (bdc, node));
    }
    else
      fprintf (file, "assert %d\n", bdcid (bdc, node));
  }
}

void
btor_dumpbtor_dump_node (Btor *btor, FILE *file, BtorNode *exp)
{
  assert (btor);
  assert (file);
  assert (exp);

  BtorDumpContext *bdc;

  bdc = btor_dumpbtor_new_dump_context (btor);
  btor_dumpbtor_add_root_to_dump_context (bdc, exp);
  btor_dumpbtor_dump_bdc (bdc, file);
  btor_dumpbtor_delete_dump_context (bdc);
}

void
btor_dumpbtor_dump_nodes (Btor *btor, FILE *file, BtorNode **roots, int nroots)
{
  assert (btor);
  assert (file);
  assert (roots);
  assert (nroots > 0);

  int i;
  BtorDumpContext *bdc;

  bdc = btor_dumpbtor_new_dump_context (btor);

  for (i = 0; i < nroots; i++)
    btor_dumpbtor_add_root_to_dump_context (bdc, roots[i]);

  btor_dumpbtor_dump_bdc (bdc, file);
  btor_dumpbtor_delete_dump_context (bdc);
}

void
btor_dumpbtor_dump (Btor *btor, FILE *file, int version)
{
  assert (btor);
  assert (file);
  assert (version == 1 || version == 2);
  // FIXME: why do we not allow these flags?
  //        inc_enabled -> ok if no assumptions
  //  assert (!btor->inc_enabled);
  (void) version;

  BtorNode *tmp;
  BtorDumpContext *bdc;
  BtorPtrHashTableIterator it;

  bdc          = btor_dumpbtor_new_dump_context (btor);
  bdc->version = 1;  // NOTE: version 2 not yet supported

  if (btor->inconsistent)
  {
    tmp = btor_false_exp (btor);
    btor_dumpbtor_add_root_to_dump_context (bdc, tmp);
    btor_release_exp (btor, tmp);
  }
  else if (btor->unsynthesized_constraints->count == 0
           && btor->synthesized_constraints->count == 0)
  {
    tmp = btor_true_exp (btor);
    btor_dumpbtor_add_root_to_dump_context (bdc, tmp);
    btor_release_exp (btor, tmp);
  }
  else
  {
    btor_iter_hashptr_init (&it, btor->unsynthesized_constraints);
    btor_iter_hashptr_queue (&it, btor->synthesized_constraints);
    while (btor_iter_hashptr_has_next (&it))
      btor_dumpbtor_add_root_to_dump_context (bdc,
                                              btor_iter_hashptr_next (&it));
  }

  btor_dumpbtor_dump_bdc (bdc, file);
  btor_dumpbtor_delete_dump_context (bdc);
}

bool
btor_dumpbtor_can_be_dumped (Btor *btor)
{
  BtorNode *cur;
  BtorPtrHashTableIterator it;

  btor_iter_hashptr_init (&it, btor->ufs);
  while (btor_iter_hashptr_has_next (&it))
  {
    cur = btor_iter_hashptr_next (&it);
    if (!btor_is_uf_array_node (cur)) return false;
  }
  return true;
}
