/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "aigprop.h"
#include "utils/btorinthash.h"
#include "utils/btoriter.h"
#include "utils/btorstack.h"

int
aigprop_sat (BtorPtrHashTable *roots)
{
}

static int
get_assignment_aig (BtorPtrHashTable *model, BtorAIG *aig)
{
  assert (amgr);
  assert (btor_find_in_ptr_hash_table (model, BTOR_REAL_ADDR_AIG (aig)));

  int res;

  if (aig == BTOR_AIG_TRUE) return 1;
  if (aig == BTOR_AIG_FALSE) return -1;
  if (BTOR_REAL_ADDR_AIG (aig)->cnf_id == 0) return 0;

  res = btor_find_in_ptr_hash_table (model, BTOR_REAL_ADDR_AIG (aig));
  if (BTOR_IS_INVERTED_AIG (aig)) res *= -1;
  return res;
}

static void
recursively_compute_assignment (BtorAIGMgr *amgr,
                                BtorPtrHashTable *model,
                                BtorAIG *aig)
{
  assert (amgr);
  assert (model);
  assert (aig);

  BtorAIG *cur, *real_cur, *left, *right, *ass;
  BtorAIGPtrStack *stack;
  BtorIntHashTable *cache;

  BTOR_INIT_STACK (stack);
  cache = btor_new_int_hash_table (mm);

  if (!BTOR_IS_CONST_AIG (aig)) BTOR_PUSH_STACK (mm, stack, aig);
  while (!BTOR_EMPTY_STACK (stack))
  {
    cur      = BTOR_POP_STACK (stack);
    real_cur = BTOR_REAL_ADDR_AIG (cur);
    assert (!BTOR_IS_CONST_AIG (real_cur));
    if (btor_find_in_ptr_hash_table (model, real_cur)) continue;

    if (BTOR_IS_VAR_AIG (real_cur))
    {
      /* initialize with false */
      btor_insert_in_ptr_hash_table (model, btor_copy_aig (amgr, real_cur))
          ->data.asInt = -1;
    }
    else
    {
      assert (BTOR_IS_AND_AIG (real_cur));
      left  = BTOR_LEFT_CHILD_AIG (real_cur);
      right = BTOR_RIGHT_CHILD_AIG (real_cur);

      if (!btor_contains_int_hash_table (cache, real_cur->id))
      {
              assert (BTOR_IS_CONST_AIG (left)
		      || !btor_contains_int_hash_table (
			      cache, BTOR_REAL_ADDR_NODE (left)->id);
	      assert (BTOR_IS_CONST_AIG (right)
		      || !btor_contains_int_hash_table (
			      cache, BTOR_REAL_ADDR_NODE (right)->id);

	      BTOR_PUSH_STACK (mm, stack, cur);
	      if (!BTOR_IS_CONST_AIG (left))
		BTOR_PUSH_STACK (mm, stack, left);
	      if (!BTOR_IS_CONST_AIG (right))
		BTOR_PUSH_STACK (mm, stack, right);
	      btor_add_int_hash_table (cache, real_cur->id);
      }
      else
      {
        if (get_assignment_aig (model, left) < 0
            || get_assignment_aig (model, right) < 0)
          btor_insert_in_ptr_hash_table (model, btor_copy_aig (amgr, real_cur))
              ->data.asInt = -1;
        else
          btor_insert_in_ptr_hash_table (model, btor_copy_aig (amgr, real_cur))
              ->data.asInt = 1;
      }
    }
  }

  btor_free_int_hash_table (cache);
  BTOR_RELEASE_STACK (mm, stack);
}

void
aigprop_generate_model (BtorAIGMgr *amgr,
                        BtorPtrHashTable *roots,
                        BtorPtrHashTable *model)
{
  assert (amgr);
  assert (roots);
  assert (model);

  BtorHashTableIterator it;

  btor_init_hash_table_iterator (&it, roots);
  while (btor_has_next_hash_table_iterator (&it))
    recursively_compute_assignment (
        amgr, model, btor_next_hash_table_iterator (&it));
}

void
aigprop_move (BtorAIGMgr *amgr,
              BtorPtrHashTable *roots,
              BtorPtrHashTable *model)
{
  assert (amgr);
  assert (roots);
  assert (model);

  // TODO
}
