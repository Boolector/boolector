/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2014 Armin Biere.
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2012-2017 Aina Niemetz.
 *  Copyright (C) 2012-2017 Mathias Preiner.
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

typedef struct BtorDumpContextState BtorDumpContextState;

struct BtorDumpContextState
{
  BtorNode *state;
  BtorNode *init;
  BtorNode *next;
};

struct BtorDumpContext
{
  uint32_t maxid;
  uint32_t maxsortid;
  uint32_t version;
  Btor *btor;
  BtorPtrHashTable *idtab;
  BtorPtrHashTable *inputs;
  BtorPtrHashTable *states;
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
                                        (BtorHashPtr) btor_node_hash_by_id,
                                        (BtorCmpPtr) btor_node_compare_by_id);
  res->states  = btor_hashptr_table_new (btor->mm,
                                        (BtorHashPtr) btor_node_hash_by_id,
                                        (BtorCmpPtr) btor_node_compare_by_id);
  res->idtab   = btor_hashptr_table_new (btor->mm,
                                       (BtorHashPtr) btor_node_hash_by_id,
                                       (BtorCmpPtr) btor_node_compare_by_id);
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
    btor_node_release (bdc->btor, BTOR_POP_STACK (bdc->roots));
  BTOR_RELEASE_STACK (bdc->roots);

  while (!BTOR_EMPTY_STACK (bdc->outputs))
    btor_node_release (bdc->btor, BTOR_POP_STACK (bdc->outputs));
  BTOR_RELEASE_STACK (bdc->outputs);

  while (!BTOR_EMPTY_STACK (bdc->bads))
    btor_node_release (bdc->btor, BTOR_POP_STACK (bdc->bads));
  BTOR_RELEASE_STACK (bdc->bads);

  while (!BTOR_EMPTY_STACK (bdc->constraints))
    btor_node_release (bdc->btor, BTOR_POP_STACK (bdc->constraints));
  BTOR_RELEASE_STACK (bdc->constraints);

  btor_iter_hashptr_init (&it, bdc->inputs);
  while (btor_iter_hashptr_has_next (&it))
    btor_node_release (bdc->btor, btor_iter_hashptr_next (&it));
  btor_hashptr_table_delete (bdc->inputs);

  btor_iter_hashptr_init (&it, bdc->states);
  while (btor_iter_hashptr_has_next (&it))
  {
    BtorDumpContextState *l = it.bucket->data.as_ptr;
    btor_node_release (bdc->btor, l->state);
    if (l->next) btor_node_release (bdc->btor, l->next);
    if (l->init) btor_node_release (bdc->btor, l->init);
    BTOR_DELETE (bdc->btor->mm, l);
    (void) btor_iter_hashptr_next (&it);
  }
  btor_hashptr_table_delete (bdc->states);

  btor_iter_hashptr_init (&it, bdc->idtab);
  while (btor_iter_hashptr_has_next (&it))
    btor_node_release (bdc->btor, btor_iter_hashptr_next (&it));
  btor_hashptr_table_delete (bdc->idtab);

  btor_hashptr_table_delete (bdc->sorts);
  btor_hashptr_table_delete (bdc->no_dump);
  BTOR_DELETE (bdc->btor->mm, bdc);
}

void
btor_dumpbtor_add_input_to_dump_context (BtorDumpContext *bdc, BtorNode *input)
{
  assert (btor_node_is_regular (input));
  assert (btor_node_is_bv_var (input));
  assert (!btor_hashptr_table_get (bdc->inputs, input));
  assert (!btor_hashptr_table_get (bdc->states, input));
  (void) btor_node_copy (bdc->btor, input);
  (void) btor_hashptr_table_add (bdc->inputs, input);
}

void
btor_dumpbtor_add_state_to_dump_context (BtorDumpContext *bdc, BtorNode *state)
{
  BtorPtrHashBucket *b;
  BtorDumpContextState *bdcl;
  assert (btor_node_is_regular (state));
  assert (btor_node_is_bv_var (state));
  assert (!btor_hashptr_table_get (bdc->inputs, state));
  assert (!btor_hashptr_table_get (bdc->states, state));
  b = btor_hashptr_table_add (bdc->states, state);
  BTOR_CNEW (bdc->btor->mm, bdcl);
  bdcl->state    = btor_node_copy (bdc->btor, state);
  b->data.as_ptr = bdcl;
}

void
btor_dumpbtor_add_next_to_dump_context (BtorDumpContext *bdc,
                                        BtorNode *state,
                                        BtorNode *next)
{
  BtorDumpContextState *l;
  BtorPtrHashBucket *b;
  b = btor_hashptr_table_get (bdc->states, state);
  assert (b);
  l = b->data.as_ptr;
  assert (l);
  assert (l->state == state);
  assert (!l->next);
  l->next = btor_node_copy (bdc->btor, next);
}

void
btor_dumpbtor_add_init_to_dump_context (BtorDumpContext *bdc,
                                        BtorNode *state,
                                        BtorNode *init)
{
  BtorDumpContextState *l;
  BtorPtrHashBucket *b;
  b = btor_hashptr_table_get (bdc->states, state);
  assert (b);
  l = b->data.as_ptr;
  assert (l);
  assert (l->state == state);
  assert (!l->init);
  l->init = btor_node_copy (bdc->btor, init);
}

void
btor_dumpbtor_add_bad_to_dump_context (BtorDumpContext *bdc, BtorNode *bad)
{
  (void) btor_node_copy (bdc->btor, bad);
  BTOR_PUSH_STACK (bdc->bads, bad);
}

void
btor_dumpbtor_add_output_to_dump_context (BtorDumpContext *bdc,
                                          BtorNode *output)
{
  (void) btor_node_copy (bdc->btor, output);
  BTOR_PUSH_STACK (bdc->outputs, output);
}

void
btor_dumpbtor_add_root_to_dump_context (BtorDumpContext *bdc, BtorNode *root)
{
  (void) btor_node_copy (bdc->btor, root);
  BTOR_PUSH_STACK (bdc->roots, root);
}

void
btor_dumpbtor_add_constraint_to_dump_context (BtorDumpContext *bdc,
                                              BtorNode *constraint)
{
  (void) btor_node_copy (bdc->btor, constraint);
  BTOR_PUSH_STACK (bdc->constraints, constraint);
}

static int32_t
bdcid (BtorDumpContext *bdc, BtorNode *node)
{
  BtorPtrHashBucket *b;
  BtorNode *real;
  int32_t res;
  real = btor_node_real_addr (node);
  b    = btor_hashptr_table_get (bdc->idtab, real);
  if (!b)
  {
    b = btor_hashptr_table_add (bdc->idtab, btor_node_copy (bdc->btor, node));
    if (btor_opt_get (bdc->btor, BTOR_OPT_PRETTY_PRINT))
      b->data.as_int = ++bdc->maxid;
    else
      b->data.as_int = real->id;
  }
  res = b->data.as_int;
  if (!btor_node_is_regular (node)) res = -res;
  return res;
}

static uint32_t
bdcsortid (BtorDumpContext *bdc, BtorSort *sort)
{
  assert (btor_hashptr_table_get (bdc->sorts, sort));
  return btor_hashptr_table_get (bdc->sorts, sort)->data.as_int;
}

static int32_t
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
  sort = btor_sort_get_by_id (bdc->btor, btor_node_get_sort_id (node));
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
    if (btor_node_is_lambda (p)) return true;
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
    cur = btor_node_real_addr (BTOR_POP_STACK (visit));

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
  uint32_t i;
  char *symbol, *cbits;
  const char *op;
  uint32_t opt;
  BtorNode *n, *index, *value;
  BtorArgsIterator ait;
  BtorNodeIterator nit;
  BtorPtrHashTable *rho;
  BtorBitVector *bits;

  node  = btor_node_real_addr (node);
  cbits = 0;

  /* argument nodes will not be dumped as they are purely internal nodes */
  if (btor_node_is_args (node)) return;

#if 0
  if (bdc->version == 2
      && (btor_node_is_args (node)
	  || (!BTOR_IS_FIRST_CURRIED_LAMBDA (node)
	      && BTOR_IS_CURRIED_LAMBDA_NODE (node))))
    return;
#endif

  /* do not dump parameterized nodes that belong to a "write-lambda" */
  if (btor_hashptr_table_get (bdc->no_dump, node)) return;

  switch (node->kind)
  {
    case BTOR_BV_ADD_NODE: op = "add"; break;
    case BTOR_BV_AND_NODE: op = "and"; break;
    case BTOR_BV_CONCAT_NODE: op = "concat"; break;
    case BTOR_COND_NODE: op = bdc->version == 1 ? "cond" : "ite"; break;
    case BTOR_BV_EQ_NODE:
    case BTOR_FUN_EQ_NODE: op = "eq"; break;
    case BTOR_BV_MUL_NODE: op = "mul"; break;
    case BTOR_PROXY_NODE: op = "proxy"; break;
    case BTOR_BV_SLL_NODE: op = "sll"; break;
    case BTOR_BV_SRL_NODE: op = "srl"; break;
    case BTOR_BV_UDIV_NODE: op = "udiv"; break;
    case BTOR_BV_ULT_NODE: op = "ult"; break;
    case BTOR_BV_UREM_NODE: op = "urem"; break;
    case BTOR_BV_SLICE_NODE: op = "slice"; break;
    case BTOR_UF_NODE:
      op = btor_node_is_uf_array (node) ? "array" : "uf";
      break;
    case BTOR_CONST_NODE:
      bits = btor_node_bv_const_get_bits (node);
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
    case BTOR_FORALL_NODE: op = "forall"; break;
    case BTOR_EXISTS_NODE: op = "exists"; break;
    case BTOR_LAMBDA_NODE:
      if (btor_opt_get (bdc->btor, BTOR_OPT_REWRITE_LEVEL) == 0
          && btor_node_lambda_get_static_rho (node))
      {
        op = "write";
        mark_no_dump (bdc, node->e[1]);
      }
      else if (bdc->version == 1
               || btor_node_fun_get_arity (bdc->btor, node) == 1)
        op = "lambda";
      else
        op = "fun";
      break;
    case BTOR_APPLY_NODE:
      if (btor_node_is_uf_array (node->e[0])
          || (btor_opt_get (bdc->btor, BTOR_OPT_REWRITE_LEVEL) == 0
              && btor_node_is_lambda (node->e[0])
              && btor_node_lambda_get_static_rho (node->e[0])))
        op = "read";
      else
        op = "apply";
      break;
    case BTOR_ARGS_NODE: op = "args"; break;
    case BTOR_UPDATE_NODE: op = "write"; break;
    default: assert (node->kind == BTOR_VAR_NODE); op = "var";
  }

  /* print id, operator and sort */
  if (bdc->version == 1)
  {
    fprintf (file, "%d %s", bdcid (bdc, node), op);

    /* print index bit width of arrays */
    if (btor_node_is_uf_array (node) || btor_node_is_fun_cond (node)
        || btor_node_is_update (node))
    {
      fprintf (file, " %d", btor_node_fun_get_width (bdc->btor, node));
      fprintf (file, " %d", btor_node_array_get_index_width (bdc->btor, node));
    }
    else if (btor_node_is_lambda (node))
    {
      fprintf (file, " %d", btor_node_fun_get_width (bdc->btor, node));
      fprintf (file, " %d", btor_node_bv_get_width (bdc->btor, node->e[0]));
    }
    else if (!btor_node_is_uf (node))
      fprintf (file, " %d", btor_node_bv_get_width (bdc->btor, node));

    if (btor_node_is_apply (node))
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

    if (btor_node_is_apply (node))
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
      fprintf (file, " %d", bdcid (bdc, btor_node_binder_get_body (node)));
      goto DONE;
    }
  }

  /* print children or const values */
  if (cbits)
  {
    fprintf (file, " %s", cbits);
    btor_mem_freestr (bdc->btor->mm, cbits);
  }
  else if (btor_node_is_proxy (node))
    fprintf (file, " %d", bdcid (bdc, node->simplified));
  /* print write instead of lambda */
  else if (btor_opt_get (bdc->btor, BTOR_OPT_REWRITE_LEVEL) == 0
           && btor_node_is_lambda (node)
           && btor_node_lambda_get_static_rho (node))
  {
    assert (btor_node_fun_get_arity (bdc->btor, node) == 1);
    rho = btor_node_lambda_get_static_rho (node);
    assert (rho->count == 1);
    index = rho->first->key;
    value = rho->first->data.as_ptr;
    assert (value);
    assert (btor_node_is_regular (index));
    assert (btor_node_is_args (index));
    assert (btor_node_is_regular (node->e[1]));
    assert (btor_node_is_bv_cond (node->e[1]));
    assert (btor_node_is_regular (node->e[1]->e[2]));
    assert (btor_node_is_apply (node->e[1]->e[2]));
    fprintf (file,
             " %d %d %d",
             bdcid (bdc, node->e[1]->e[2]->e[0]),
             bdcid (bdc, index->e[0]),
             bdcid (bdc, value));
  }
  else if (btor_node_is_update (node))
  {
    fprintf (file, " %d", bdcid (bdc, node->e[0]));
    fprintf (file, " %d", bdcid (bdc, node->e[1]->e[0]));
    fprintf (file, " %d", bdcid (bdc, node->e[2]));
  }
  else
    for (i = 0; i < node->arity; i++)
      fprintf (file, " %d", bdcid (bdc, node->e[i]));

  /* print slice limits/var symbols */
  if (node->kind == BTOR_BV_SLICE_NODE)
    fprintf (file,
             " %d %d",
             btor_node_bv_slice_get_upper (node),
             btor_node_bv_slice_get_lower (node));
  else if (btor_node_is_bv_var (node) || btor_node_is_uf (node)
           || btor_node_is_param (node))
  {
    symbol = btor_node_get_symbol (bdc->btor, node);
    if (symbol) fprintf (file, " %s", symbol);
  }
DONE:
  fputc ('\n', file);
}

static void
bdcsort (BtorDumpContext *bdc, BtorSort *sort, FILE *file)
{
  uint32_t i, id;
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
  uint32_t i;
  BtorMemMgr *mm;
  BtorNodePtrStack work;
  BtorSortPtrStack sorts;
  BtorNode *cur;
  BtorSort *sort;
  BtorPtrHashTable *mark_nodes, *mark_sorts;

  mm         = bdc->btor->mm;
  mark_nodes = btor_hashptr_table_new (mm,
                                       (BtorHashPtr) btor_node_hash_by_id,
                                       (BtorCmpPtr) btor_node_compare_by_id);
  mark_sorts = btor_hashptr_table_new (mm, 0, 0);

  BTOR_INIT_STACK (mm, sorts);
  BTOR_INIT_STACK (mm, work);
  BTOR_PUSH_STACK (work, start);

  while (!BTOR_EMPTY_STACK (work))
  {
    cur = btor_node_real_addr (BTOR_POP_STACK (work));

    if (btor_hashptr_table_get (mark_nodes, cur)) continue;

    (void) btor_hashptr_table_add (mark_nodes, cur);

    sort = btor_sort_get_by_id (bdc->btor, btor_node_get_sort_id (cur));

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
  uint32_t i;

  if (bdc->version == 2) bdcsorts (bdc, start, file);

  assert (BTOR_EMPTY_STACK (bdc->work));

  BTOR_PUSH_STACK (bdc->work, start);
  while (!BTOR_EMPTY_STACK (bdc->work))
  {
    node = BTOR_POP_STACK (bdc->work);
    if (node)
    {
      node = btor_node_real_addr (node);
      if (btor_hashptr_table_get (bdc->idtab, node)) continue;
      BTOR_PUSH_STACK (bdc->work, node);
      BTOR_PUSH_STACK (bdc->work, 0);

      for (i = 1; i <= node->arity; i++)
        BTOR_PUSH_STACK (bdc->work, node->e[node->arity - i]);

      if (node->simplified) BTOR_PUSH_STACK (bdc->work, node->simplified);
    }
    else
    {
      assert (!BTOR_EMPTY_STACK (bdc->work));
      node = BTOR_POP_STACK (bdc->work);
      assert (btor_node_is_regular (node));
      (void) bdcid (bdc, node);
      bdcnode (bdc, node, file);
    }
  }
}

void
btor_dumpbtor_dump_bdc (BtorDumpContext *bdc, FILE *file)
{
  BtorPtrHashTableIterator it;
  uint32_t i;
  char *symbol;
  int32_t id;
  uint32_t len;

  btor_iter_hashptr_init (&it, bdc->inputs);
  while (btor_iter_hashptr_has_next (&it))
  {
    BtorNode *node = btor_iter_hashptr_next (&it);
    assert (node);
    assert (btor_node_is_regular (node));
    assert (btor_node_is_bv_var (node));
    id = bdcid (bdc, node);
    fprintf (file, "%d input %u", id, btor_node_bv_get_width (bdc->btor, node));
    if ((symbol = btor_node_get_symbol (bdc->btor, node)))
      fprintf (file, " %s", symbol);
    fputc ('\n', file);
  }

  btor_iter_hashptr_init (&it, bdc->states);
  while (btor_iter_hashptr_has_next (&it))
  {
    BtorNode *node = btor_iter_hashptr_next (&it);
    assert (node);
    assert (btor_node_is_regular (node));
    assert (btor_node_is_bv_var (node));
    id = bdcid (bdc, node);
    fprintf (file, "%d state %u", id, btor_node_bv_get_width (bdc->btor, node));
    if ((symbol = btor_node_get_symbol (bdc->btor, node)))
      fprintf (file, " %s", symbol);
    fputc ('\n', file);
  }

  btor_iter_hashptr_init (&it, bdc->states);
  while (btor_iter_hashptr_has_next (&it))
  {
    BtorDumpContextState *bdcl = it.bucket->data.as_ptr;
    assert (bdcl->state);
    assert (btor_node_is_regular (bdcl->state));
    assert (btor_node_is_bv_var (bdcl->state));
    if (bdcl->next)
    {
      bdcrec (bdc, bdcl->next, file);
      id = ++bdc->maxid;
      fprintf (file,
               "%d next %u %d %d\n",
               id,
               btor_node_bv_get_width (bdc->btor, bdcl->next),
               bdcid (bdc, bdcl->state),
               bdcid (bdc, bdcl->next));
    }
    if (bdcl->init)
    {
      bdcrec (bdc, bdcl->init, file);
      id = ++bdc->maxid;
      fprintf (file,
               "%d init %u %d %d\n",
               id,
               btor_node_bv_get_width (bdc->btor, bdcl->init),
               bdcid (bdc, bdcl->state),
               bdcid (bdc, bdcl->init));
    }
    (void) btor_iter_hashptr_next (&it);
  }

  for (i = 0; i < BTOR_COUNT_STACK (bdc->outputs); i++)
  {
    BtorNode *node = BTOR_PEEK_STACK (bdc->outputs, i);
    bdcrec (bdc, node, file);
    id = ++bdc->maxid;
    fprintf (file,
             "%d output %u %d\n",
             id,
             btor_node_bv_get_width (bdc->btor, node),
             bdcid (bdc, node));
  }

  for (i = 0; i < BTOR_COUNT_STACK (bdc->bads); i++)
  {
    BtorNode *node = BTOR_PEEK_STACK (bdc->bads, i);
    bdcrec (bdc, node, file);
    id = ++bdc->maxid;
    fprintf (file,
             "%d bad %u %d\n",
             id,
             btor_node_bv_get_width (bdc->btor, node),
             bdcid (bdc, node));
  }

  for (i = 0; i < BTOR_COUNT_STACK (bdc->constraints); i++)
  {
    BtorNode *node = BTOR_PEEK_STACK (bdc->constraints, i);
    bdcrec (bdc, node, file);
    id = ++bdc->maxid;
    fprintf (file,
             "%d constraint %u %d\n",
             id,
             btor_node_bv_get_width (bdc->btor, node),
             bdcid (bdc, node));
  }

  for (i = 0; i < BTOR_COUNT_STACK (bdc->roots); i++)
  {
    BtorNode *node = BTOR_PEEK_STACK (bdc->roots, i);
    bdcrec (bdc, node, file);
    id = ++bdc->maxid;
    if (bdc->version == 1)
    {
      if (btor_sort_is_fun (bdc->btor, btor_node_get_sort_id (node)))
        len = btor_node_fun_get_width (bdc->btor, node);
      else
        len = btor_node_bv_get_width (bdc->btor, node);
      fprintf (file, "%d root %u %d\n", id, len, bdcid (bdc, node));
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
btor_dumpbtor_dump_nodes (Btor *btor,
                          FILE *file,
                          BtorNode **roots,
                          uint32_t nroots)
{
  assert (btor);
  assert (file);
  assert (roots);
  assert (nroots > 0);

  uint32_t i;
  BtorDumpContext *bdc;

  bdc = btor_dumpbtor_new_dump_context (btor);

  for (i = 0; i < nroots; i++)
    btor_dumpbtor_add_root_to_dump_context (bdc, roots[i]);

  btor_dumpbtor_dump_bdc (bdc, file);
  btor_dumpbtor_delete_dump_context (bdc);
}

void
btor_dumpbtor_dump (Btor *btor, FILE *file, uint32_t version)
{
  assert (btor);
  assert (file);
  assert (version == 1 || version == 2);
  (void) version;

  BtorNode *tmp;
  BtorDumpContext *bdc;
  BtorPtrHashTableIterator it;

  bdc          = btor_dumpbtor_new_dump_context (btor);
  bdc->version = 1;  // NOTE: version 2 not yet supported

  if (btor->inconsistent)
  {
    tmp = btor_exp_false (btor);
    btor_dumpbtor_add_root_to_dump_context (bdc, tmp);
    btor_node_release (btor, tmp);
  }
  else if (btor->unsynthesized_constraints->count == 0
           && btor->synthesized_constraints->count == 0
           && btor->embedded_constraints->count == 0)
  {
    tmp = btor_exp_true (btor);
    btor_dumpbtor_add_root_to_dump_context (bdc, tmp);
    btor_node_release (btor, tmp);
  }
  else
  {
    btor_iter_hashptr_init (&it, btor->unsynthesized_constraints);
    btor_iter_hashptr_queue (&it, btor->synthesized_constraints);
    btor_iter_hashptr_queue (&it, btor->embedded_constraints);
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
    if (!btor_node_is_uf_array (cur)) return false;
  }
  return true;
}
