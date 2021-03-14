/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2019 Mathias Preiner.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "preprocess/btorpputils.h"

#include "btorcore.h"
#include "utils/btorhashint.h"

void
btor_pputils_collect_lambdas (Btor *btor, BtorNodePtrStack *lambdas)
{
  assert (btor);
  assert (lambdas);

  uint32_t i;
  BtorNode *cur;
  BtorNodePtrStack visit;
  BtorPtrHashTableIterator it;
  BtorIntHashTable *cache;

  cache = btor_hashint_table_new (btor->mm);
  BTOR_INIT_STACK (btor->mm, visit);
  btor_iter_hashptr_init (&it, btor->synthesized_constraints);
  btor_iter_hashptr_queue (&it, btor->unsynthesized_constraints);
  btor_iter_hashptr_queue (&it, btor->assumptions);
  while (btor_iter_hashptr_has_next (&it))
  {
    BTOR_PUSH_STACK (visit, btor_iter_hashptr_next (&it));
  }

  while (!BTOR_EMPTY_STACK (visit))
  {
    cur = btor_node_real_addr (BTOR_POP_STACK (visit));

    if (btor_hashint_table_contains (cache, cur->id) || !cur->lambda_below)
      continue;

    btor_hashint_table_add (cache, cur->id);
    if (btor_node_is_lambda (cur)) BTOR_PUSH_STACK (*lambdas, cur);

    for (i = 0; i < cur->arity; i++) BTOR_PUSH_STACK (visit, cur->e[i]);
  }

  btor_hashint_table_delete (cache);
  BTOR_RELEASE_STACK (visit);
}
