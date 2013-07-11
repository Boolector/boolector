/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2013 Armin Biere.
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2012-2013 Aina Niemetz, Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btordump2.h"
#include "btorconst.h"
#include "btorexp.h"
#include "btorhash.h"
#include "btormem.h"
#include "btorstack.h"

typedef struct BtorDumpContextLatch BtorDumpContextLatch;

struct BtorDumpContextLatch
{
  BtorNode *latch, *init, *next;
};

struct BtorDumpContext
{
  int maxid;
  Btor *btor;
  BtorPtrHashTable *idtab, *inputs, *latches;
  BtorNodePtrStack outputs, bads, constraints, roots, work;
};

BtorDumpContext *
btor_new_dump_context (Btor *btor)
{
  BtorDumpContext *res;
  BTOR_CNEW (btor->mm, res);
  res->btor    = btor;
  res->inputs  = btor_new_ptr_hash_table (btor->mm,
                                         (BtorHashPtr) btor_hash_exp_by_id,
                                         (BtorCmpPtr) btor_compare_exp_by_id);
  res->latches = btor_new_ptr_hash_table (btor->mm,
                                          (BtorHashPtr) btor_hash_exp_by_id,
                                          (BtorCmpPtr) btor_compare_exp_by_id);
  res->idtab   = btor_new_ptr_hash_table (btor->mm,
                                        (BtorHashPtr) btor_hash_exp_by_id,
                                        (BtorCmpPtr) btor_compare_exp_by_id);
  return res;
}

void
btor_delete_dump_context (BtorDumpContext *bdc)
{
  BtorPtrHashBucket *b;

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

  for (b = bdc->inputs->first; b; b = b->next)
    btor_release_exp (bdc->btor, b->key);
  btor_delete_ptr_hash_table (bdc->inputs);

  for (b = bdc->latches->first; b; b = b->next)
  {
    BtorDumpContextLatch *l = b->data.asPtr;
    btor_release_exp (bdc->btor, l->latch);
    if (l->next) btor_release_exp (bdc->btor, l->next);
    if (l->init) btor_release_exp (bdc->btor, l->init);
    BTOR_DELETE (bdc->btor->mm, l);
  }
  btor_delete_ptr_hash_table (bdc->latches);

  for (b = bdc->idtab->first; b; b = b->next)
    btor_release_exp (bdc->btor, b->key);
  btor_delete_ptr_hash_table (bdc->idtab);

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
    b             = btor_insert_in_ptr_hash_table (bdc->idtab,
                                       btor_copy_exp (bdc->btor, node));
    b->data.asInt = ++bdc->maxid;
  }
  res = b->data.asInt;
  if (!BTOR_IS_REGULAR_NODE (node)) res = -res;
  return res;
}

static void
bdcnode (BtorDumpContext *bdc, BtorNode *node, FILE *file)
{
  char idbuffer[20];
  const char *op;
  BtorNode *n;
  int j;

  n = BTOR_REAL_ADDR_NODE (node);

  assert (btor_find_in_ptr_hash_table (bdc->idtab, n));

  fprintf (file, "%d ", bdcid (bdc, n));

  switch (n->kind)
  {
    case BTOR_ADD_NODE: op = "add"; goto PRINT;
    case BTOR_AND_NODE: op = "and"; goto PRINT;
    case BTOR_CONCAT_NODE: op = "concat"; goto PRINT;
    case BTOR_BCOND_NODE: op = "cond"; goto PRINT;
    case BTOR_BEQ_NODE:
    case BTOR_AEQ_NODE: op = "eq"; goto PRINT;
    case BTOR_MUL_NODE: op = "mul"; goto PRINT;
    case BTOR_PROXY_NODE: op = "proxy"; goto PRINT;
    case BTOR_READ_NODE: op = "read"; goto PRINT;
    case BTOR_SLL_NODE: op = "sll"; goto PRINT;
    case BTOR_SRL_NODE: op = "srl"; goto PRINT;
    case BTOR_UDIV_NODE: op = "udiv"; goto PRINT;
    case BTOR_ULT_NODE: op = "ult"; goto PRINT;
    case BTOR_UREM_NODE:
      op = "urem";
    PRINT:
      fputs (op, file);
      fprintf (file, " %d", n->len);

      if (n->kind == BTOR_PROXY_NODE)
        fprintf (file, " %d", bdcid (bdc, n->simplified));
      else
        for (j = 0; j < n->arity; j++)
          fprintf (file, " %d", bdcid (bdc, n->e[j]));
      break;

    case BTOR_SLICE_NODE:
      fprintf (file,
               "slice %d %d %d %d",
               n->len,
               bdcid (bdc, n->e[0]),
               n->upper,
               n->lower);
      break;

    case BTOR_ARRAY_VAR_NODE:
      fprintf (file, "array %d %d", n->len, n->index_len);
      break;

    case BTOR_WRITE_NODE:
      fprintf (file,
               "write %d %d %d %d %d",
               n->len,
               n->index_len,
               bdcid (bdc, n->e[0]),
               bdcid (bdc, n->e[1]),
               bdcid (bdc, n->e[2]));
      break;

    case BTOR_ACOND_NODE:
      fprintf (file,
               "acond %d %d %d %d %d",
               n->len,
               n->index_len,
               bdcid (bdc, n->e[0]),
               bdcid (bdc, n->e[1]),
               bdcid (bdc, n->e[2]));
      break;

    case BTOR_BV_CONST_NODE:
      if (btor_is_zero_const (n->bits))
        fprintf (file, "zero %d", n->len);
      else if (btor_is_one_const (n->bits))
        fprintf (file, "one %d", n->len);
      else if (btor_is_ones_const (n->bits))
        fprintf (file, "ones %d", n->len);
      else
        fprintf (file, "const %d %s", n->len, n->bits);
      break;

    case BTOR_PARAM_NODE: fprintf (file, "param %d", n->len); break;

    case BTOR_LAMBDA_NODE:
      fprintf (file,
               "lambda %d %d %d %d",
               n->len,
               n->index_len,
               bdcid (bdc, n->e[0]),
               bdcid (bdc, n->e[1]));
      break;

    default:
      assert (n->kind == BTOR_BV_VAR_NODE);
      fprintf (file, "var %d", n->len);
      sprintf (idbuffer, "%d", n->id);
      assert (n->symbol);
      if (strcmp (n->symbol, idbuffer)) fprintf (file, " %s", n->symbol);
      break;
  }

  fputc ('\n', file);
}

static void
bdcrec (BtorDumpContext *bdc, BtorNode *start, FILE *file)
{
  BtorNode *node;
  int i;

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
btor_dump_btor (BtorDumpContext *bdc, FILE *file)
{
  BtorPtrHashBucket *b;
  int i;

  for (b = bdc->inputs->first; b; b = b->next)
  {
    BtorNode *node = b->key;
    int id;
    assert (node);
    assert (BTOR_IS_REGULAR_NODE (node));
    assert (BTOR_IS_BV_VAR_NODE (node));
    id = bdcid (bdc, node);
    fprintf (file, "%d input %d", id, node->len);
    if (node->symbol) fprintf (file, " %s", node->symbol);
    fputc ('\n', file);
  }

  for (b = bdc->latches->first; b; b = b->next)
  {
    BtorNode *node = b->key;
    int id;
    assert (node);
    assert (BTOR_IS_REGULAR_NODE (node));
    assert (BTOR_IS_BV_VAR_NODE (node));
    id = bdcid (bdc, node);
    fprintf (file, "%d latch %d", id, node->len);
    if (node->symbol) fprintf (file, " %s", node->symbol);
    fputc ('\n', file);
  }

  for (b = bdc->latches->first; b; b = b->next)
  {
    BtorDumpContextLatch *bdcl = b->data.asPtr;
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
    fprintf (file,
             "%d root %d %d\n",
             id,
             btor_get_exp_len (bdc->btor, node),
             bdcid (bdc, node));
  }
}
