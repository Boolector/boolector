/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2013 Armin Biere.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btordump.h"
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
  int maxidx;
  Btor* btor;
  BtorPtrHashTable *idtab, *inputs, *latches;
  BtorNodePtrStack roots, bads, constraints;
};

BtorDumpContext*
btor_new_dump_context (Btor* btor)
{
  BtorDumpContext* res;
  BTOR_CNEW (btor->mm, res);
  res->btor    = btor;
  res->inputs  = btor_new_ptr_hash_table (btor->mm,
                                         (BtorHashPtr) btor_hash_exp_by_id,
                                         (BtorCmpPtr) btor_compare_exp_by_id);
  res->latches = btor_new_ptr_hash_table (btor->mm,
                                          (BtorHashPtr) btor_hash_exp_by_id,
                                          (BtorCmpPtr) btor_compare_exp_by_id);
  return res;
}

void
btor_delete_dump_context (BtorDumpContext* bdc)
{
  BtorPtrHashBucket* b;

  while (!BTOR_EMPTY_STACK (bdc->roots))
    btor_release_exp (bdc->btor, BTOR_POP_STACK (bdc->roots));
  BTOR_RELEASE_STACK (bdc->btor->mm, bdc->roots);

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
    BtorDumpContextLatch* l = b->data.asPtr;
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
btor_add_input_to_dump_context (BtorDumpContext* bdc, BtorNode* input)
{
  assert (BTOR_IS_REGULAR_NODE (input));
  assert (BTOR_IS_BV_VAR_NODE (input));
  assert (!btor_find_in_ptr_hash_table (bdc->inputs, input));
  (void) btor_copy_exp (bdc->btor, input);
  (void) btor_insert_in_ptr_hash_table (bdc->inputs, input);
}

void
btor_add_next_to_dump_context (BtorDumpContext* bdc,
                               BtorNode* latch,
                               BtorNode* next)
{
  BtorDumpContextLatch* l;
  BtorPtrHashBucket* b;
  b = btor_find_in_ptr_hash_table (bdc->latches, latch);
  assert (b);
  l = b->data.asPtr;
  assert (l);
  assert (l->latch == latch);
  assert (!l->next);
  l->next = btor_copy_exp (bdc->btor, next);
}

void
btor_add_init_to_dump_context (BtorDumpContext* bdc,
                               BtorNode* latch,
                               BtorNode* init)
{
  BtorDumpContextLatch* l;
  BtorPtrHashBucket* b;
  b = btor_find_in_ptr_hash_table (bdc->latches, latch);
  assert (b);
  l = b->data.asPtr;
  assert (l);
  assert (l->latch == latch);
  assert (!l->init);
  l->init = btor_copy_exp (bdc->btor, init);
}

void
btor_add_bad_to_dump_context (BtorDumpContext* bdc, BtorNode* bad)
{
  (void) btor_copy_exp (bdc->btor, bad);
  BTOR_PUSH_STACK (bdc->btor->mm, bdc->bads, bad);
}

void
btor_add_root_to_dump_context (BtorDumpContext* bdc, BtorNode* root)
{
  (void) btor_copy_exp (bdc->btor, root);
  BTOR_PUSH_STACK (bdc->btor->mm, bdc->roots, root);
}

void
btor_add_constraint_to_dump_context (BtorDumpContext* bdc, BtorNode* constraint)
{
  (void) btor_copy_exp (bdc->btor, constraint);
  BTOR_PUSH_STACK (bdc->btor->mm, bdc->constraints, constraint);
}

void
btor_dump_btor (BtorDumpContext* btor, FILE* file)
{
}
