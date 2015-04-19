/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2014 Armin Biere.
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2012-2014 Aina Niemetz.
 *  Copyright (C) 2012-2015 Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btordumpbtor.h"
#include "btorconst.h"
#include "btorcore.h"
#include "btorsort.h"
#include "utils/btorhash.h"
#include "utils/btoriter.h"
#include "utils/btormem.h"
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
};

BtorDumpContext *
btor_new_dump_context (Btor *btor)
{
  BtorDumpContext *res;
  BTOR_CNEW (btor->mm, res);
  res->btor    = btor;
  res->version = 1;
  res->inputs  = btor_new_ptr_hash_table (btor->mm,
                                         (BtorHashPtr) btor_hash_exp_by_id,
                                         (BtorCmpPtr) btor_compare_exp_by_id);
  res->latches = btor_new_ptr_hash_table (btor->mm,
                                          (BtorHashPtr) btor_hash_exp_by_id,
                                          (BtorCmpPtr) btor_compare_exp_by_id);
  res->idtab   = btor_new_ptr_hash_table (btor->mm,
                                        (BtorHashPtr) btor_hash_exp_by_id,
                                        (BtorCmpPtr) btor_compare_exp_by_id);
  res->sorts   = btor_new_ptr_hash_table (btor->mm, 0, 0);

  /* set start id for roots */
  if (!btor->options.pretty_print.val)
    res->maxid = BTOR_COUNT_STACK (btor->nodes_id_table);

  return res;
}

void
btor_delete_dump_context (BtorDumpContext *bdc)
{
  BtorHashTableIterator it;

  BTOR_RELEASE_STACK (bdc->btor->mm, bdc->work);

  while (!BTOR_EMPTY_STACK (bdc->roots))
    btor_release_exp (bdc->btor, BTOR_POP_STACK (bdc->roots));
  BTOR_RELEASE_STACK (bdc->btor->mm, bdc->roots);

  while (!BTOR_EMPTY_STACK (bdc->outputs))
    btor_release_exp (bdc->btor, BTOR_POP_STACK (bdc->outputs));
  BTOR_RELEASE_STACK (bdc->btor->mm, bdc->outputs);

  while (!BTOR_EMPTY_STACK (bdc->bads))
    btor_release_exp (bdc->btor, BTOR_POP_STACK (bdc->bads));
  BTOR_RELEASE_STACK (bdc->btor->mm, bdc->bads);

  while (!BTOR_EMPTY_STACK (bdc->constraints))
    btor_release_exp (bdc->btor, BTOR_POP_STACK (bdc->constraints));
  BTOR_RELEASE_STACK (bdc->btor->mm, bdc->constraints);

  init_node_hash_table_iterator (&it, bdc->inputs);
  while (has_next_node_hash_table_iterator (&it))
    btor_release_exp (bdc->btor, next_node_hash_table_iterator (&it));
  btor_delete_ptr_hash_table (bdc->inputs);

  init_node_hash_table_iterator (&it, bdc->latches);
  while (has_next_node_hash_table_iterator (&it))
  {
    BtorDumpContextLatch *l = it.bucket->data.asPtr;
    btor_release_exp (bdc->btor, l->latch);
    if (l->next) btor_release_exp (bdc->btor, l->next);
    if (l->init) btor_release_exp (bdc->btor, l->init);
    BTOR_DELETE (bdc->btor->mm, l);
    (void) next_node_hash_table_iterator (&it);
  }
  btor_delete_ptr_hash_table (bdc->latches);

  init_node_hash_table_iterator (&it, bdc->idtab);
  while (has_next_node_hash_table_iterator (&it))
    btor_release_exp (bdc->btor, next_node_hash_table_iterator (&it));
  btor_delete_ptr_hash_table (bdc->idtab);

  init_hash_table_iterator (&it, bdc->sorts);
  while (has_next_hash_table_iterator (&it))
    btor_release_sort (&bdc->btor->sorts_unique_table,
                       (BtorSort *) next_hash_table_iterator (&it));
  btor_delete_ptr_hash_table (bdc->sorts);

  BTOR_DELETE (bdc->btor->mm, bdc);
}

void
btor_add_input_to_dump_context (BtorDumpContext *bdc, BtorNode *input)
{
  assert (BTOR_IS_REGULAR_NODE (input));
  assert (BTOR_IS_BV_VAR_NODE (input));
  assert (!btor_find_in_ptr_hash_table (bdc->inputs, input));
  assert (!btor_find_in_ptr_hash_table (bdc->latches, input));
  (void) btor_copy_exp (bdc->btor, input);
  (void) btor_insert_in_ptr_hash_table (bdc->inputs, input);
}

void
btor_add_latch_to_dump_context (BtorDumpContext *bdc, BtorNode *latch)
{
  BtorPtrHashBucket *b;
  BtorDumpContextLatch *bdcl;
  assert (BTOR_IS_REGULAR_NODE (latch));
  assert (BTOR_IS_BV_VAR_NODE (latch));
  assert (!btor_find_in_ptr_hash_table (bdc->inputs, latch));
  assert (!btor_find_in_ptr_hash_table (bdc->latches, latch));
  b = btor_insert_in_ptr_hash_table (bdc->latches, latch);
  BTOR_CNEW (bdc->btor->mm, bdcl);
  bdcl->latch   = btor_copy_exp (bdc->btor, latch);
  b->data.asPtr = bdcl;
}

void
btor_add_next_to_dump_context (BtorDumpContext *bdc,
                               BtorNode *latch,
                               BtorNode *next)
{
  BtorDumpContextLatch *l;
  BtorPtrHashBucket *b;
  b = btor_find_in_ptr_hash_table (bdc->latches, latch);
  assert (b);
  l = b->data.asPtr;
  assert (l);
  assert (l->latch == latch);
  assert (!l->next);
  l->next = btor_copy_exp (bdc->btor, next);
}

void
btor_add_init_to_dump_context (BtorDumpContext *bdc,
                               BtorNode *latch,
                               BtorNode *init)
{
  BtorDumpContextLatch *l;
  BtorPtrHashBucket *b;
  b = btor_find_in_ptr_hash_table (bdc->latches, latch);
  assert (b);
  l = b->data.asPtr;
  assert (l);
  assert (l->latch == latch);
  assert (!l->init);
  l->init = btor_copy_exp (bdc->btor, init);
}

void
btor_add_bad_to_dump_context (BtorDumpContext *bdc, BtorNode *bad)
{
  (void) btor_copy_exp (bdc->btor, bad);
  BTOR_PUSH_STACK (bdc->btor->mm, bdc->bads, bad);
}

void
btor_add_output_to_dump_context (BtorDumpContext *bdc, BtorNode *output)
{
  (void) btor_copy_exp (bdc->btor, output);
  BTOR_PUSH_STACK (bdc->btor->mm, bdc->outputs, output);
}

void
btor_add_root_to_dump_context (BtorDumpContext *bdc, BtorNode *root)
{
  (void) btor_copy_exp (bdc->btor, root);
  BTOR_PUSH_STACK (bdc->btor->mm, bdc->roots, root);
}

void
btor_add_constraint_to_dump_context (BtorDumpContext *bdc, BtorNode *constraint)
{
  (void) btor_copy_exp (bdc->btor, constraint);
  BTOR_PUSH_STACK (bdc->btor->mm, bdc->constraints, constraint);
}

static int
bdcid (BtorDumpContext *bdc, BtorNode *node)
{
  BtorPtrHashBucket *b;
  BtorNode *real;
  int res;
  real = BTOR_REAL_ADDR_NODE (node);
  b    = btor_find_in_ptr_hash_table (bdc->idtab, real);
  if (!b)
  {
    b = btor_insert_in_ptr_hash_table (bdc->idtab,
                                       btor_copy_exp (bdc->btor, node));
    if (bdc->btor->options.pretty_print.val)
      b->data.asInt = ++bdc->maxid;
    else
      b->data.asInt = real->id;
  }
  res = b->data.asInt;
  if (!BTOR_IS_REGULAR_NODE (node)) res = -res;
  return res;
}

static int
bdcsortid (BtorDumpContext *bdc, BtorSort *sort)
{
  assert (btor_find_in_ptr_hash_table (bdc->sorts, sort));
  return btor_find_in_ptr_hash_table (bdc->sorts, sort)->data.asInt;
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
  sort = btor_create_or_get_sort (node->btor, node);
  assert (btor_find_in_ptr_hash_table (bdc->sorts, sort));
  assert (sort->refs > 1);
  btor_release_sort (&bdc->btor->sorts_unique_table, sort);
  return sort;
}

#ifndef NDEBUG
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
#endif

static void
bdcnode (BtorDumpContext *bdc, BtorNode *node, FILE *file)
{
  int i, aspi = -1;
  char *symbol;
  const char *op;
  BtorNode *n;
  BtorArgsIterator ait;
  BtorNodeIterator nit;

  node = BTOR_REAL_ADDR_NODE (node);

  /* argument nodes will not be dumped as they are purely internal nodes */
  if (BTOR_IS_ARGS_NODE (node)) return;

#if 0
  if (bdc->version == 2
      && (BTOR_IS_ARGS_NODE (node)
	  || (!BTOR_IS_FIRST_CURRIED_LAMBDA (node)
	      && BTOR_IS_CURRIED_LAMBDA_NODE (node))))
    return;
#endif

  switch (node->kind)
  {
    case BTOR_ADD_NODE: op = "add"; break;
    case BTOR_AND_NODE: op = "and"; break;
    case BTOR_CONCAT_NODE: op = "concat"; break;
    case BTOR_BCOND_NODE: op = bdc->version == 1 ? "cond" : "ite"; break;
    case BTOR_BEQ_NODE:
    case BTOR_FEQ_NODE: op = "eq"; break;
    case BTOR_MUL_NODE: op = "mul"; break;
    case BTOR_PROXY_NODE: op = "proxy"; break;
    case BTOR_SLL_NODE: op = "sll"; break;
    case BTOR_SRL_NODE: op = "srl"; break;
    case BTOR_UDIV_NODE: op = "udiv"; break;
    case BTOR_ULT_NODE: op = "ult"; break;
    case BTOR_UREM_NODE: op = "urem"; break;
    case BTOR_SLICE_NODE: op = "slice"; break;
    case BTOR_UF_NODE:
      op = BTOR_IS_UF_ARRAY_NODE (node) ? "array" : "uf";
      break;
    case BTOR_BV_CONST_NODE:
      if (btor_is_zero_const (node->bits))
        op = "zero";
      else if (btor_is_one_const (node->bits))
        op = "one";
      else if (btor_is_ones_const (node->bits))
        op = "ones";
      else if ((aspi = btor_is_small_positive_int_const (node->bits)) > 0)
        op = "constd";
      else
        op = "const";
      break;
    case BTOR_PARAM_NODE: op = "param"; break;
    case BTOR_LAMBDA_NODE:
      if (bdc->version == 1 || btor_get_fun_arity (bdc->btor, node) == 1)
        op = "lambda";
      else
        op = "fun";
      break;
    case BTOR_APPLY_NODE:
      if (BTOR_IS_UF_ARRAY_NODE (node->e[0]))
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
    fprintf (file, "%d %s %d", bdcid (bdc, node), op, node->len);

    /* print index bit width of arrays */
    if (BTOR_IS_UF_ARRAY_NODE (node) || BTOR_IS_LAMBDA_NODE (node))
      fprintf (file, " %d", BTOR_ARRAY_INDEX_LEN (node));

    if (BTOR_IS_APPLY_NODE (node))
    {
      fprintf (file, " %d", bdcid (bdc, node->e[0]));
      init_args_iterator (&ait, node->e[1]);
      while (has_next_args_iterator (&ait))
        fprintf (file, " %d", bdcid (bdc, next_args_iterator (&ait)));
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

    if (BTOR_IS_APPLY_NODE (node))
    {
      fprintf (file, " %d", bdcid (bdc, node->e[0]));
      init_args_iterator (&ait, node->e[1]);
      while (has_next_args_iterator (&ait))
        fprintf (file, " %d", bdcid (bdc, next_args_iterator (&ait)));
      goto DONE;
    }
    else if (strcmp (op, "fun") == 0)
    {
      assert (!has_lambda_parent (node));
      init_lambda_iterator (&nit, node);
      while (has_next_lambda_iterator (&nit))
      {
        n = next_lambda_iterator (&nit);
        fprintf (
            file, " %d", bdcid (bdc, (BtorNode *) BTOR_LAMBDA_GET_PARAM (n)));
      }
      fprintf (file, " %d", bdcid (bdc, BTOR_LAMBDA_GET_BODY (node)));
      goto DONE;
    }
  }

  /* print children or const values */
  if (strcmp (op, "const") == 0)
    fprintf (file, " %s", node->bits);
  else if (strcmp (op, "constd") == 0)
    fprintf (file, " %d", aspi);
  else if (BTOR_IS_PROXY_NODE (node))
    fprintf (file, " %d", bdcid (bdc, node->simplified));
  else
    for (i = 0; i < node->arity; i++)
      fprintf (file, " %d", bdcid (bdc, node->e[i]));

  /* print slice limits/var symbols */
  if (node->kind == BTOR_SLICE_NODE)
    fprintf (file, " %d %d", node->upper, node->lower);
  else if (BTOR_IS_BV_VAR_NODE (node) || BTOR_IS_UF_NODE (node))
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
  int i, id;
  const char *kind;

  /* already dumped */
  if (btor_find_in_ptr_hash_table (bdc->sorts, sort)) return;

  switch (sort->kind)
  {
    default:
    case BTOR_BOOL_SORT: kind = "bool"; break;
    case BTOR_BITVEC_SORT: kind = "bv"; break;
    case BTOR_ARRAY_SORT: kind = "array"; break;
    case BTOR_FUN_SORT: kind = "fun"; break;
  }

  id = sort->id;
  if (bdc->btor->options.pretty_print.val) id = ++bdc->maxsortid;

  fprintf (file, "%d sort %s", id, kind);

  if (sort->kind == BTOR_BITVEC_SORT)
    fprintf (file, " %d", sort->bitvec.len);
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

  btor_insert_in_ptr_hash_table (bdc->sorts, sort)->data.asInt = id;
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
  mark_nodes = btor_new_ptr_hash_table (mm,
                                        (BtorHashPtr) btor_hash_exp_by_id,
                                        (BtorCmpPtr) btor_compare_exp_by_id);
  mark_sorts = btor_new_ptr_hash_table (mm, 0, 0);

  BTOR_INIT_STACK (sorts);
  BTOR_INIT_STACK (work);
  BTOR_PUSH_STACK (mm, work, start);

  while (!BTOR_EMPTY_STACK (work))
  {
    cur = BTOR_REAL_ADDR_NODE (BTOR_POP_STACK (work));

    if (btor_find_in_ptr_hash_table (mark_nodes, cur)) continue;

    (void) btor_insert_in_ptr_hash_table (mark_nodes, cur);

    sort = btor_create_or_get_sort (bdc->btor, cur);

    if (btor_find_in_ptr_hash_table (bdc->sorts, sort)
        || btor_find_in_ptr_hash_table (mark_sorts, sort))
      btor_release_sort (&bdc->btor->sorts_unique_table, sort);
    else
    {
      (void) btor_insert_in_ptr_hash_table (mark_sorts, sort);
      BTOR_PUSH_STACK (mm, sorts, sort);
    }

    for (i = 0; i < cur->arity; i++) BTOR_PUSH_STACK (mm, work, cur->e[i]);
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

  btor_delete_ptr_hash_table (mark_nodes);
  btor_delete_ptr_hash_table (mark_sorts);
  BTOR_RELEASE_STACK (mm, sorts);
  BTOR_RELEASE_STACK (mm, work);
}

static void
bdcrec (BtorDumpContext *bdc, BtorNode *start, FILE *file)
{
  BtorNode *node;
  int i;

  if (bdc->version == 2) bdcsorts (bdc, start, file);

  assert (BTOR_EMPTY_STACK (bdc->work));

  BTOR_PUSH_STACK (bdc->btor->mm, bdc->work, start);
  while (!BTOR_EMPTY_STACK (bdc->work))
  {
    node = BTOR_POP_STACK (bdc->work);
    if (node)
    {
      node = BTOR_REAL_ADDR_NODE (node);
      if (btor_find_in_ptr_hash_table (bdc->idtab, node)) continue;
      BTOR_PUSH_STACK (bdc->btor->mm, bdc->work, node);
      BTOR_PUSH_STACK (bdc->btor->mm, bdc->work, 0);

      for (i = node->arity - 1; i >= 0; i--)
        BTOR_PUSH_STACK (bdc->btor->mm, bdc->work, node->e[i]);

      if (node->simplified)
        BTOR_PUSH_STACK (bdc->btor->mm, bdc->work, node->simplified);
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
btor_dump_btor_bdc (BtorDumpContext *bdc, FILE *file)
{
  BtorHashTableIterator it;
  int i;
  char *symbol;

  init_node_hash_table_iterator (&it, bdc->inputs);
  while (has_next_node_hash_table_iterator (&it))
  {
    BtorNode *node = next_node_hash_table_iterator (&it);
    int id;
    assert (node);
    assert (BTOR_IS_REGULAR_NODE (node));
    assert (BTOR_IS_BV_VAR_NODE (node));
    id = bdcid (bdc, node);
    fprintf (file, "%d input %d", id, node->len);
    if ((symbol = btor_get_symbol_exp (bdc->btor, node)))
      fprintf (file, " %s", symbol);
    fputc ('\n', file);
  }

  init_node_hash_table_iterator (&it, bdc->latches);
  while (has_next_node_hash_table_iterator (&it))
  {
    BtorNode *node = next_node_hash_table_iterator (&it);
    int id;
    assert (node);
    assert (BTOR_IS_REGULAR_NODE (node));
    assert (BTOR_IS_BV_VAR_NODE (node));
    id = bdcid (bdc, node);
    fprintf (file, "%d latch %d", id, node->len);
    if ((symbol = btor_get_symbol_exp (bdc->btor, node)))
      fprintf (file, " %s", symbol);
    fputc ('\n', file);
  }

  init_node_hash_table_iterator (&it, bdc->latches);
  while (has_next_node_hash_table_iterator (&it))
  {
    BtorDumpContextLatch *bdcl = it.bucket->data.asPtr;
    int id;
    assert (bdcl->latch);
    assert (BTOR_IS_REGULAR_NODE (bdcl->latch));
    assert (BTOR_IS_BV_VAR_NODE (bdcl->latch));
    if (bdcl->next)
    {
      bdcrec (bdc, bdcl->next, file);
      id = ++bdc->maxid;
      fprintf (file,
               "%d next %d %d %d\n",
               id,
               btor_get_exp_len (bdc->btor, bdcl->next),
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
               btor_get_exp_len (bdc->btor, bdcl->init),
               bdcid (bdc, bdcl->latch),
               bdcid (bdc, bdcl->init));
    }
    (void) next_node_hash_table_iterator (&it);
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
             btor_get_exp_len (bdc->btor, node),
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
             btor_get_exp_len (bdc->btor, node),
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
             btor_get_exp_len (bdc->btor, node),
             bdcid (bdc, node));
  }

  for (i = 0; i < BTOR_COUNT_STACK (bdc->roots); i++)
  {
    BtorNode *node = BTOR_PEEK_STACK (bdc->roots, i);
    int id;
    bdcrec (bdc, node, file);
    id = ++bdc->maxid;
    if (bdc->version == 1)
      fprintf (file,
               "%d root %d %d\n",
               id,
               btor_get_exp_len (bdc->btor, node),
               bdcid (bdc, node));
    else
      fprintf (file, "assert %d\n", bdcid (bdc, node));
  }
}

void
btor_dump_btor_node (Btor *btor, FILE *file, BtorNode *exp)
{
  assert (btor);
  assert (file);
  assert (exp);

  BtorDumpContext *bdc;

  bdc = btor_new_dump_context (btor);
  btor_add_root_to_dump_context (bdc, exp);
  btor_dump_btor_bdc (bdc, file);
  btor_delete_dump_context (bdc);
}

void
btor_dump_btor_nodes (Btor *btor, FILE *file, BtorNode **roots, int nroots)
{
  assert (btor);
  assert (file);
  assert (roots);
  assert (nroots > 0);

  int i;
  BtorDumpContext *bdc;

  bdc = btor_new_dump_context (btor);

  for (i = 0; i < nroots; i++) btor_add_root_to_dump_context (bdc, roots[i]);

  btor_dump_btor_bdc (bdc, file);
  btor_delete_dump_context (bdc);
}

void
btor_dump_btor (Btor *btor, FILE *file, int version)
{
  assert (btor);
  assert (file);
  assert (version == 1 || version == 2);
  // FIXME: why do we not allow these flags?
  //        inc_enabled -> ok if no assumptions
  //        model_gen -> ??
  //  assert (!btor->inc_enabled);
  //  assert (!btor->model_gen);
  (void) version;

  int ret;
  BtorNode *temp;
  BtorDumpContext *bdc;
  BtorHashTableIterator it;

  ret          = btor_simplify (btor);
  bdc          = btor_new_dump_context (btor);
  bdc->version = 1;  // NOTE: version 2 not yet supported

  if (ret == BTOR_UNKNOWN)
  {
    init_node_hash_table_iterator (&it, btor->unsynthesized_constraints);
    queue_node_hash_table_iterator (&it, btor->synthesized_constraints);
    queue_node_hash_table_iterator (&it, btor->embedded_constraints);
    while (has_next_node_hash_table_iterator (&it))
      btor_add_root_to_dump_context (bdc, next_node_hash_table_iterator (&it));
  }
  else
  {
    assert (ret == BTOR_SAT || ret == BTOR_UNSAT);
    temp = (ret == BTOR_SAT) ? btor_true_exp (btor) : btor_false_exp (btor);
    btor_add_root_to_dump_context (bdc, temp);
    btor_release_exp (btor, temp);
  }

  btor_dump_btor_bdc (bdc, file);
  btor_delete_dump_context (bdc);
}

int
btor_can_be_dumped (Btor *btor)
{
  BtorNode *cur;
  BtorHashTableIterator it;

  init_node_hash_table_iterator (&it, btor->ufs);
  while (has_next_node_hash_table_iterator (&it))
  {
    cur = next_node_hash_table_iterator (&it);
    if (!BTOR_IS_UF_ARRAY_NODE (cur)) return 0;
  }
  return 1;
}
