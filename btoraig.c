/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2014 Armin Biere.
 *  Copyright (C) 2013-2014 Aina Niemetz.
 *  Copyright (C) 2013-2015 Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btoraig.h"
#include "btorexit.h"
#include "btorsat.h"
#include "utils/btorhash.h"
#include "utils/btormap.h"
#include "utils/btorutil.h"

#include <assert.h>
#include <limits.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>

/*------------------------------------------------------------------------*/

#define BTOR_ABORT_AIG(cond, msg)            \
  do                                         \
  {                                          \
    if (cond)                                \
    {                                        \
      fputs ("[btoraig] " msg "\n", stdout); \
      exit (BTOR_ERR_EXIT);                  \
    }                                        \
  } while (0)

#define BTOR_INIT_AIG_UNIQUE_TABLE(mm, table) \
  do                                          \
  {                                           \
    assert (mm);                              \
    (table).size         = 1;                 \
    (table).num_elements = 0;                 \
    BTOR_CNEW (mm, (table).chains);           \
  } while (0)

#define BTOR_RELEASE_AIG_UNIQUE_TABLE(mm, table)     \
  do                                                 \
  {                                                  \
    assert (mm);                                     \
    BTOR_DELETEN (mm, (table).chains, (table).size); \
  } while (0)

#define BTOR_AIG_UNIQUE_TABLE_LIMIT 30

#define BTOR_AIG_UNIQUE_TABLE_PRIME 2000000137u

#define BTOR_FIND_AND_AIG_CONTRADICTION_LIMIT 8

//#define BTOR_EXTRACT_TOP_LEVEL_MULTI_OR

//#define NBTOR_AIG_SORT

/*------------------------------------------------------------------------*/

static void
setup_aig_and_add_to_id_table (BtorAIGMgr *amgr, BtorAIG *aig)
{
  int32_t id;

  id = BTOR_COUNT_STACK (amgr->id2aig);
  BTOR_ABORT_AIG (id == INT_MAX, "AIG id overflow");
  aig->refs = 1;
  aig->id   = id;
  BTOR_PUSH_STACK (amgr->mm, amgr->id2aig, aig);
  assert (BTOR_COUNT_STACK (amgr->id2aig) == aig->id + 1);
  assert (BTOR_PEEK_STACK (amgr->id2aig, aig->id) == aig);
}

static BtorAIG *
new_and_aig (BtorAIGMgr *amgr, BtorAIG *left, BtorAIG *right)
{
  assert (amgr);
  assert (!BTOR_IS_CONST_AIG (left));
  assert (!BTOR_IS_CONST_AIG (right));

  BtorAIG *aig;
  size_t size;

  size = sizeof (BtorAIG) + 2 * sizeof (int32_t);
  aig  = btor_malloc (amgr->mm, size);
  memset (aig, 0, size);
  setup_aig_and_add_to_id_table (amgr, aig);
  aig->children[0] = BTOR_GET_AIG_ID_AIG (left);
  aig->children[1] = BTOR_GET_AIG_ID_AIG (right);
  amgr->cur_num_aigs++;
  if (amgr->max_num_aigs < amgr->cur_num_aigs)
    amgr->max_num_aigs = amgr->cur_num_aigs;
  return aig;
}

static void
btor_release_cnf_id_aig_mgr (BtorAIGMgr *amgr, BtorAIG *aig)
{
  assert (!BTOR_IS_INVERTED_AIG (aig));
  assert (aig->cnf_id > 0);
  assert (aig->cnf_id < BTOR_SIZE_STACK (amgr->cnfid2aig));
  assert (amgr->cnfid2aig.start[aig->cnf_id] == aig->id);
  amgr->cnfid2aig.start[aig->cnf_id] = 0;
  btor_release_cnf_id_sat_mgr (amgr->smgr, aig->cnf_id);
  aig->cnf_id = 0;
}

static void
delete_aig_node (BtorAIGMgr *amgr, BtorAIG *aig)
{
  assert (!BTOR_IS_INVERTED_AIG (aig));
  assert (amgr);
  if (BTOR_IS_CONST_AIG (aig)) return;
  if (aig->cnf_id) btor_release_cnf_id_aig_mgr (amgr, aig);
  amgr->id2aig.start[aig->id] = 0;
  if (aig->is_var)
  {
    amgr->cur_num_aig_vars--;
    BTOR_DELETE (amgr->mm, aig);
  }
  else
  {
    amgr->cur_num_aigs--;
    btor_free (amgr->mm, aig, sizeof (BtorAIG) + 2 * sizeof (int32_t));
  }
}

static unsigned int
compute_aig_hash (BtorAIG *aig, int table_size)
{
  unsigned int hash;
  assert (!BTOR_IS_INVERTED_AIG (aig));
  assert (BTOR_IS_AND_AIG (aig));
  assert (table_size > 0);
  assert (btor_is_power_of_2_util (table_size));
  hash = (unsigned int) abs (aig->children[0]) + abs (aig->children[1]);
  //    (unsigned int) BTOR_REAL_ADDR_AIG (BTOR_RIGHT_CHILD_AIG (aig))->id;
  hash = (hash * BTOR_AIG_UNIQUE_TABLE_PRIME) & (table_size - 1);
  return hash;
}

static void
delete_aig_nodes_unique_table_entry (BtorAIGMgr *amgr, BtorAIG *aig)
{
  unsigned int hash;
  BtorAIG *cur, *prev;
  assert (amgr);
  assert (!BTOR_IS_INVERTED_AIG (aig));
  assert (BTOR_IS_AND_AIG (aig));
  prev = 0;
  hash = compute_aig_hash (aig, amgr->table.size);
  cur  = BTOR_GET_NODE_AIG (amgr->table.chains[hash]);
  while (cur != aig)
  {
    assert (!BTOR_IS_INVERTED_AIG (cur));
    prev = cur;
    cur  = BTOR_GET_NODE_AIG (cur->next);
  }
  assert (cur);
  if (!prev)
    amgr->table.chains[hash] = cur->next;
  else
    prev->next = cur->next;
  amgr->table.num_elements--;
}

static void
inc_aig_ref_counter (BtorAIG *aig)
{
  if (!BTOR_IS_CONST_AIG (aig))
  {
    BTOR_ABORT_AIG (BTOR_REAL_ADDR_AIG (aig)->refs == UINT_MAX,
                    "reference counter overflow");
    BTOR_REAL_ADDR_AIG (aig)->refs++;
  }
}

static BtorAIG *
inc_aig_ref_counter_and_return (BtorAIG *aig)
{
  inc_aig_ref_counter (aig);
  return aig;
}

static int32_t *
find_and_aig (BtorAIGMgr *amgr, BtorAIG *left, BtorAIG *right)
{
  BtorAIG *cur, *temp;
  unsigned int hash;
  int32_t *result;
  assert (amgr);
  assert (!BTOR_IS_CONST_AIG (left));
  assert (!BTOR_IS_CONST_AIG (right));
  hash = (((unsigned int) BTOR_REAL_ADDR_AIG (left)->id
           + (unsigned int) BTOR_REAL_ADDR_AIG (right)->id)
          * BTOR_AIG_UNIQUE_TABLE_PRIME)
         & (amgr->table.size - 1);
  result = amgr->table.chains + hash;
  cur    = BTOR_GET_NODE_AIG (*result);
#ifndef NBTOR_AIG_SORT
  if (BTOR_REAL_ADDR_AIG (right)->id < BTOR_REAL_ADDR_AIG (left)->id)
  {
    temp  = left;
    left  = right;
    right = temp;
  }
#endif
  while (cur)
  {
    assert (!BTOR_IS_INVERTED_AIG (cur));
    assert (BTOR_IS_AND_AIG (cur));
#ifdef NBTOR_AIG_SORT
    if ((BTOR_LEFT_CHILD_AIG (cur) == left
         && BTOR_RIGHT_CHILD_AIG (cur) == right)
        || (BTOR_LEFT_CHILD_AIG (cur) == right
            && BTOR_RIGHT_CHILD_AIG (cur) == left))
      break;
#else
    if (BTOR_LEFT_CHILD_AIG (cur) == left
        && BTOR_RIGHT_CHILD_AIG (cur) == right)
      break;
#endif
    else
    {
      result = &cur->next;
      cur    = cur->next == 0 ? 0 : BTOR_GET_NODE_AIG (cur->next);
    }
  }
  return result;
}

static void
enlarge_aig_nodes_unique_table (BtorAIGMgr *amgr)
{
  BtorMemMgr *mm;
  int32_t *new_chains;
  int i, size, new_size;
  unsigned int hash;
  BtorAIG *temp = 0;
  BtorAIG *cur  = 0;
  assert (amgr);
  size     = amgr->table.size;
  new_size = size << 1;
  assert (new_size / size == 2);
  mm = amgr->mm;
  BTOR_CNEWN (mm, new_chains, new_size);
  for (i = 0; i < size; i++)
  {
    cur = BTOR_GET_NODE_AIG (amgr->table.chains[i]);
    while (cur)
    {
      assert (!BTOR_IS_INVERTED_AIG (cur));
      assert (BTOR_IS_AND_AIG (cur));
      temp             = BTOR_GET_NODE_AIG (cur->next);
      hash             = compute_aig_hash (cur, new_size);
      cur->next        = new_chains[hash];
      new_chains[hash] = cur->id;
      cur              = temp;
    }
  }
  BTOR_RELEASE_AIG_UNIQUE_TABLE (mm, amgr->table);
  amgr->table.size   = new_size;
  amgr->table.chains = new_chains;
}

BtorAIG *
btor_copy_aig (BtorAIGMgr *amgr, BtorAIG *aig)
{
  assert (amgr);
  (void) amgr;
  if (BTOR_IS_CONST_AIG (aig)) return aig;
  return inc_aig_ref_counter_and_return (aig);
}

void
btor_release_aig (BtorAIGMgr *amgr, BtorAIG *aig)
{
  BtorAIG *cur, *l, *r;
  BtorAIGPtrStack stack;
  BtorMemMgr *mm;

  assert (amgr);
  mm = amgr->mm;

  if (!BTOR_IS_CONST_AIG (aig))
  {
    cur = BTOR_REAL_ADDR_AIG (aig);
    assert (cur->refs > 0u);
    if (cur->refs > 1u)
    {
      cur->refs--;
    }
    else
    {
      assert (cur->refs == 1u);
      BTOR_INIT_STACK (stack);
      goto BTOR_RELEASE_AIG_WITHOUT_POP;

      while (!BTOR_EMPTY_STACK (stack))
      {
        cur = BTOR_POP_STACK (stack);
        cur = BTOR_REAL_ADDR_AIG (cur);

        if (cur->refs > 1u)
        {
          cur->refs--;
        }
        else
        {
        BTOR_RELEASE_AIG_WITHOUT_POP:
          assert (cur->refs == 1u);
          if (!BTOR_IS_VAR_AIG (cur))
          {
            assert (BTOR_IS_AND_AIG (cur));
            l = BTOR_LEFT_CHILD_AIG (cur);
            r = BTOR_RIGHT_CHILD_AIG (cur);
            BTOR_PUSH_STACK (mm, stack, r);
            BTOR_PUSH_STACK (mm, stack, l);
            delete_aig_nodes_unique_table_entry (amgr, cur);
          }

          delete_aig_node (amgr, cur);
        }
      }
      BTOR_RELEASE_STACK (mm, stack);
    }
  }
}

BtorAIG *
btor_var_aig (BtorAIGMgr *amgr)
{
  BtorAIG *aig;
  assert (amgr);
  BTOR_CNEW (amgr->mm, aig);
  setup_aig_and_add_to_id_table (amgr, aig);
  aig->is_var = 1;
  amgr->cur_num_aig_vars++;
  amgr->num_aig_vars++;
  return aig;
}

BtorAIG *
btor_not_aig (BtorAIGMgr *amgr, BtorAIG *aig)
{
  assert (amgr);
  (void) amgr;
  inc_aig_ref_counter (aig);
  return BTOR_INVERT_AIG (aig);
}

static int
find_and_contradiction_aig (
    BtorAIGMgr *amgr, BtorAIG *aig, BtorAIG *a0, BtorAIG *a1, int *calls)
{
  assert (amgr);
  assert (aig);
  assert (a0);
  assert (a1);
  assert (calls);
  assert (*calls >= 0);
  (void) amgr;

  if (*calls >= BTOR_FIND_AND_AIG_CONTRADICTION_LIMIT) return 0;

  if (!BTOR_IS_INVERTED_AIG (aig) && BTOR_IS_AND_AIG (aig))
  {
    if (BTOR_LEFT_CHILD_AIG (aig) == BTOR_INVERT_AIG (a0)
        || BTOR_LEFT_CHILD_AIG (aig) == BTOR_INVERT_AIG (a1)
        || BTOR_RIGHT_CHILD_AIG (aig) == BTOR_INVERT_AIG (a0)
        || BTOR_RIGHT_CHILD_AIG (aig) == BTOR_INVERT_AIG (a1))
      return 1;
    *calls += 1;
    return find_and_contradiction_aig (
               amgr, BTOR_LEFT_CHILD_AIG (aig), a0, a1, calls)
           || find_and_contradiction_aig (
                  amgr, BTOR_RIGHT_CHILD_AIG (aig), a0, a1, calls);
  }
  return 0;
}

static BtorAIG *
btor_simp_aig_by_sat (BtorAIGMgr *amgr, BtorAIG *aig)
{
  int lit = BTOR_GET_CNF_ID_AIG (aig), val, repr, sign;
  BtorAIG *res;
  if (!lit) return aig;
  val = btor_fixed_sat (amgr->smgr, lit);
  if (val) return (val < 0) ? BTOR_AIG_FALSE : BTOR_AIG_TRUE;
  repr = btor_repr_sat (amgr->smgr, lit);
  if ((sign = (repr < 0))) repr = -repr;
  assert (repr < BTOR_SIZE_STACK (amgr->cnfid2aig));
  res = BTOR_GET_NODE_AIG (amgr->cnfid2aig.start[repr]);
  if (!res) return aig;
  if (sign) res = BTOR_INVERT_AIG (res);
  return res;
}

BtorAIG *
btor_and_aig (BtorAIGMgr *amgr, BtorAIG *left, BtorAIG *right)
{
  BtorAIG *res, *real_left, *real_right;
  int32_t *lookup;
  int calls;

  assert (amgr);

  if (amgr->smgr->initialized)
  {
    left  = btor_simp_aig_by_sat (amgr, left);
    right = btor_simp_aig_by_sat (amgr, right);
  }

  calls = 0;

  // TODO (ma): why is BTOR_AIG_TWO_LEVEL_OPT_TRY_AGAIN not up here?
  if (left == BTOR_AIG_FALSE || right == BTOR_AIG_FALSE) return BTOR_AIG_FALSE;

  if (left == BTOR_AIG_TRUE) return inc_aig_ref_counter_and_return (right);

BTOR_AIG_TWO_LEVEL_OPT_TRY_AGAIN:
  if (right == BTOR_AIG_TRUE || (left == right))
    return inc_aig_ref_counter_and_return (left);
  if (left == BTOR_INVERT_AIG (right)) return BTOR_AIG_FALSE;
  real_left  = BTOR_REAL_ADDR_AIG (left);
  real_right = BTOR_REAL_ADDR_AIG (right);

  /* 2 level minimization rules for AIGs */
  /* first rule of contradiction */
  if (BTOR_IS_AND_AIG (real_left) && !BTOR_IS_INVERTED_AIG (left))
  {
    if (BTOR_LEFT_CHILD_AIG (real_left) == BTOR_INVERT_AIG (right)
        || BTOR_RIGHT_CHILD_AIG (real_left) == BTOR_INVERT_AIG (right))
      return BTOR_AIG_FALSE;
  }
  /* use commutativity */
  if (BTOR_IS_AND_AIG (real_right) && !BTOR_IS_INVERTED_AIG (right))
  {
    if (BTOR_LEFT_CHILD_AIG (real_right) == BTOR_INVERT_AIG (left)
        || BTOR_RIGHT_CHILD_AIG (real_right) == BTOR_INVERT_AIG (left))
      return BTOR_AIG_FALSE;
  }
  /* second rule of contradiction */
  if (BTOR_IS_AND_AIG (real_right) && BTOR_IS_AND_AIG (real_left)
      && !BTOR_IS_INVERTED_AIG (left) && !BTOR_IS_INVERTED_AIG (right))
  {
    if (BTOR_LEFT_CHILD_AIG (real_left)
            == BTOR_INVERT_AIG (BTOR_LEFT_CHILD_AIG (real_right))
        || BTOR_LEFT_CHILD_AIG (real_left)
               == BTOR_INVERT_AIG (BTOR_RIGHT_CHILD_AIG (real_right))
        || BTOR_RIGHT_CHILD_AIG (real_left)
               == BTOR_INVERT_AIG (BTOR_LEFT_CHILD_AIG (real_right))
        || BTOR_RIGHT_CHILD_AIG (real_left)
               == BTOR_INVERT_AIG (BTOR_RIGHT_CHILD_AIG (real_right)))
      return BTOR_AIG_FALSE;
  }
  /* first rule of subsumption */
  if (BTOR_IS_AND_AIG (real_left) && BTOR_IS_INVERTED_AIG (left))
  {
    if (BTOR_LEFT_CHILD_AIG (real_left) == BTOR_INVERT_AIG (right)
        || BTOR_RIGHT_CHILD_AIG (real_left) == BTOR_INVERT_AIG (right))
      return inc_aig_ref_counter_and_return (right);
  }
  /* use commutativity */
  if (BTOR_IS_AND_AIG (real_right) && BTOR_IS_INVERTED_AIG (right))
  {
    if (BTOR_LEFT_CHILD_AIG (real_right) == BTOR_INVERT_AIG (left)
        || BTOR_RIGHT_CHILD_AIG (real_right) == BTOR_INVERT_AIG (left))
      return inc_aig_ref_counter_and_return (left);
  }
  /* second rule of subsumption */
  if (BTOR_IS_AND_AIG (real_right) && BTOR_IS_AND_AIG (real_left)
      && BTOR_IS_INVERTED_AIG (left) && !BTOR_IS_INVERTED_AIG (right))
  {
    if (BTOR_LEFT_CHILD_AIG (real_left)
            == BTOR_INVERT_AIG (BTOR_LEFT_CHILD_AIG (real_right))
        || BTOR_LEFT_CHILD_AIG (real_left)
               == BTOR_INVERT_AIG (BTOR_RIGHT_CHILD_AIG (real_right))
        || BTOR_RIGHT_CHILD_AIG (real_left)
               == BTOR_INVERT_AIG (BTOR_LEFT_CHILD_AIG (real_right))
        || BTOR_RIGHT_CHILD_AIG (real_left)
               == BTOR_INVERT_AIG (BTOR_RIGHT_CHILD_AIG (real_right)))
      return inc_aig_ref_counter_and_return (right);
  }
  /* use commutativity */
  if (BTOR_IS_AND_AIG (real_right) && BTOR_IS_AND_AIG (real_left)
      && !BTOR_IS_INVERTED_AIG (left) && BTOR_IS_INVERTED_AIG (right))
  {
    if (BTOR_LEFT_CHILD_AIG (real_left)
            == BTOR_INVERT_AIG (BTOR_LEFT_CHILD_AIG (real_right))
        || BTOR_LEFT_CHILD_AIG (real_left)
               == BTOR_INVERT_AIG (BTOR_RIGHT_CHILD_AIG (real_right))
        || BTOR_RIGHT_CHILD_AIG (real_left)
               == BTOR_INVERT_AIG (BTOR_LEFT_CHILD_AIG (real_right))
        || BTOR_RIGHT_CHILD_AIG (real_left)
               == BTOR_INVERT_AIG (BTOR_RIGHT_CHILD_AIG (real_right)))
      return inc_aig_ref_counter_and_return (left);
  }
  /* rule of resolution */
  if (BTOR_IS_AND_AIG (real_right) && BTOR_IS_AND_AIG (real_left)
      && BTOR_IS_INVERTED_AIG (left) && BTOR_IS_INVERTED_AIG (right))
  {
    if ((BTOR_LEFT_CHILD_AIG (real_left) == BTOR_LEFT_CHILD_AIG (real_right)
         && BTOR_RIGHT_CHILD_AIG (real_left)
                == BTOR_INVERT_AIG (BTOR_RIGHT_CHILD_AIG (real_right)))
        || (BTOR_LEFT_CHILD_AIG (real_left) == BTOR_RIGHT_CHILD_AIG (real_right)
            && BTOR_RIGHT_CHILD_AIG (real_left)
                   == BTOR_INVERT_AIG (BTOR_LEFT_CHILD_AIG (real_right))))
      return inc_aig_ref_counter_and_return (
          BTOR_INVERT_AIG (BTOR_LEFT_CHILD_AIG (real_left)));
  }
  /* use commutativity */
  if (BTOR_IS_AND_AIG (real_right) && BTOR_IS_AND_AIG (real_left)
      && BTOR_IS_INVERTED_AIG (left) && BTOR_IS_INVERTED_AIG (right))
  {
    if ((BTOR_RIGHT_CHILD_AIG (real_right) == BTOR_RIGHT_CHILD_AIG (real_left)
         && BTOR_LEFT_CHILD_AIG (real_right)
                == BTOR_INVERT_AIG (BTOR_LEFT_CHILD_AIG (real_left)))
        || (BTOR_RIGHT_CHILD_AIG (real_right) == BTOR_LEFT_CHILD_AIG (real_left)
            && BTOR_LEFT_CHILD_AIG (real_right)
                   == BTOR_INVERT_AIG (BTOR_RIGHT_CHILD_AIG (real_left))))
      return inc_aig_ref_counter_and_return (
          BTOR_INVERT_AIG (BTOR_RIGHT_CHILD_AIG (real_right)));
  }
  /* asymmetric rule of idempotency */
  if (BTOR_IS_AND_AIG (real_left) && !BTOR_IS_INVERTED_AIG (left))
  {
    if (BTOR_LEFT_CHILD_AIG (real_left) == right
        || BTOR_RIGHT_CHILD_AIG (real_left) == right)
      return inc_aig_ref_counter_and_return (left);
  }
  /* use commutativity */
  if (BTOR_IS_AND_AIG (real_right) && !BTOR_IS_INVERTED_AIG (right))
  {
    if (BTOR_LEFT_CHILD_AIG (real_right) == left
        || BTOR_RIGHT_CHILD_AIG (real_right) == left)
      return inc_aig_ref_counter_and_return (right);
  }
  /* symmetric rule of idempotency */
  if (BTOR_IS_AND_AIG (real_right) && BTOR_IS_AND_AIG (real_left)
      && !BTOR_IS_INVERTED_AIG (left) && !BTOR_IS_INVERTED_AIG (right))
  {
    if (BTOR_LEFT_CHILD_AIG (real_left) == BTOR_LEFT_CHILD_AIG (real_right)
        || BTOR_RIGHT_CHILD_AIG (real_left) == BTOR_LEFT_CHILD_AIG (real_right))
    {
      right = BTOR_RIGHT_CHILD_AIG (real_right);
      goto BTOR_AIG_TWO_LEVEL_OPT_TRY_AGAIN;
    }
  }
  /* use commutativity */
  if (BTOR_IS_AND_AIG (real_right) && BTOR_IS_AND_AIG (real_left)
      && !BTOR_IS_INVERTED_AIG (left) && !BTOR_IS_INVERTED_AIG (right))
  {
    if (BTOR_LEFT_CHILD_AIG (real_left) == BTOR_RIGHT_CHILD_AIG (real_right)
        || BTOR_RIGHT_CHILD_AIG (real_left)
               == BTOR_RIGHT_CHILD_AIG (real_right))
    {
      right = BTOR_LEFT_CHILD_AIG (real_right);
      goto BTOR_AIG_TWO_LEVEL_OPT_TRY_AGAIN;
    }
  }
  /* asymmetric rule of substitution */
  if (BTOR_IS_AND_AIG (real_left) && BTOR_IS_INVERTED_AIG (left))
  {
    if (BTOR_RIGHT_CHILD_AIG (real_left) == right)
    {
      left = BTOR_INVERT_AIG (BTOR_LEFT_CHILD_AIG (real_left));
      goto BTOR_AIG_TWO_LEVEL_OPT_TRY_AGAIN;
    }
    if (BTOR_LEFT_CHILD_AIG (real_left) == right)
    {
      left = BTOR_INVERT_AIG (BTOR_RIGHT_CHILD_AIG (real_left));
      goto BTOR_AIG_TWO_LEVEL_OPT_TRY_AGAIN;
    }
  }
  /* use commutativity */
  if (BTOR_IS_AND_AIG (real_right) && BTOR_IS_INVERTED_AIG (right))
  {
    if (BTOR_LEFT_CHILD_AIG (real_right) == left)
    {
      right = BTOR_INVERT_AIG (BTOR_RIGHT_CHILD_AIG (real_right));
      goto BTOR_AIG_TWO_LEVEL_OPT_TRY_AGAIN;
    }
    if (BTOR_RIGHT_CHILD_AIG (real_right) == left)
    {
      right = BTOR_INVERT_AIG (BTOR_LEFT_CHILD_AIG (real_right));
      goto BTOR_AIG_TWO_LEVEL_OPT_TRY_AGAIN;
    }
  }
  /* symmetric rule of substitution */
  if (BTOR_IS_AND_AIG (real_left) && BTOR_IS_INVERTED_AIG (left)
      && BTOR_IS_AND_AIG (real_right) && !BTOR_IS_INVERTED_AIG (right))
  {
    if ((BTOR_RIGHT_CHILD_AIG (real_left) == BTOR_LEFT_CHILD_AIG (real_right))
        || (BTOR_RIGHT_CHILD_AIG (real_left)
            == BTOR_RIGHT_CHILD_AIG (real_right)))
    {
      left = BTOR_INVERT_AIG (BTOR_LEFT_CHILD_AIG (real_left));
      goto BTOR_AIG_TWO_LEVEL_OPT_TRY_AGAIN;
    }
    if ((BTOR_LEFT_CHILD_AIG (real_left) == BTOR_LEFT_CHILD_AIG (real_right))
        || (BTOR_LEFT_CHILD_AIG (real_left)
            == BTOR_RIGHT_CHILD_AIG (real_right)))
    {
      left = BTOR_INVERT_AIG (BTOR_RIGHT_CHILD_AIG (real_left));
      goto BTOR_AIG_TWO_LEVEL_OPT_TRY_AGAIN;
    }
  }
  /* use commutativity */
  if (BTOR_IS_AND_AIG (real_right) && BTOR_IS_INVERTED_AIG (right)
      && BTOR_IS_AND_AIG (real_left) && !BTOR_IS_INVERTED_AIG (left))
  {
    if ((BTOR_LEFT_CHILD_AIG (real_right) == BTOR_RIGHT_CHILD_AIG (real_left))
        || (BTOR_LEFT_CHILD_AIG (real_right)
            == BTOR_LEFT_CHILD_AIG (real_left)))
    {
      right = BTOR_INVERT_AIG (BTOR_RIGHT_CHILD_AIG (real_right));
      goto BTOR_AIG_TWO_LEVEL_OPT_TRY_AGAIN;
    }
    if ((BTOR_RIGHT_CHILD_AIG (real_right) == BTOR_RIGHT_CHILD_AIG (real_left))
        || (BTOR_RIGHT_CHILD_AIG (real_right)
            == BTOR_LEFT_CHILD_AIG (real_left)))
    {
      right = BTOR_INVERT_AIG (BTOR_LEFT_CHILD_AIG (real_right));
      goto BTOR_AIG_TWO_LEVEL_OPT_TRY_AGAIN;
    }
  }

  if (find_and_contradiction_aig (amgr, left, left, right, &calls)
      || find_and_contradiction_aig (amgr, right, left, right, &calls))
    return BTOR_AIG_FALSE;

  lookup = find_and_aig (amgr, left, right);
  assert (lookup);
  res = *lookup ? BTOR_GET_NODE_AIG (*lookup) : 0;
  if (!res)
  {
    if (amgr->table.num_elements == amgr->table.size
        && btor_log_2_util (amgr->table.size) < BTOR_AIG_UNIQUE_TABLE_LIMIT)
    {
      enlarge_aig_nodes_unique_table (amgr);
      lookup = find_and_aig (amgr, left, right);
    }
    if (real_right->id < real_left->id)
      res = new_and_aig (amgr, right, left);
    else
      res = new_and_aig (amgr, left, right);
    *lookup = res->id;
    inc_aig_ref_counter (left);
    inc_aig_ref_counter (right);
    assert (amgr->table.num_elements < INT_MAX);
    amgr->table.num_elements++;
  }
  else
  {
    inc_aig_ref_counter (res);
  }
  return res;
}

BtorAIG *
btor_or_aig (BtorAIGMgr *amgr, BtorAIG *left, BtorAIG *right)
{
  assert (amgr);
  return BTOR_INVERT_AIG (
      btor_and_aig (amgr, BTOR_INVERT_AIG (left), BTOR_INVERT_AIG (right)));
}

BtorAIG *
btor_eq_aig (BtorAIGMgr *amgr, BtorAIG *left, BtorAIG *right)
{
  BtorAIG *eq, *eq_left, *eq_right;
  assert (amgr);

  eq_left =
      BTOR_INVERT_AIG (btor_and_aig (amgr, left, BTOR_INVERT_AIG (right)));
  eq_right =
      BTOR_INVERT_AIG (btor_and_aig (amgr, BTOR_INVERT_AIG (left), right));
  eq = btor_and_aig (amgr, eq_left, eq_right);
  btor_release_aig (amgr, eq_left);
  btor_release_aig (amgr, eq_right);
  return eq;
}

BtorAIG *
btor_cond_aig (BtorAIGMgr *amgr,
               BtorAIG *a_cond,
               BtorAIG *a_if,
               BtorAIG *a_else)
{
  BtorAIG *cond, *and1, *and2;
  assert (amgr);
  and1 = btor_and_aig (amgr, a_if, a_cond);
  and2 = btor_and_aig (amgr, a_else, BTOR_INVERT_AIG (a_cond));
  cond = btor_or_aig (amgr, and1, and2);
  btor_release_aig (amgr, and1);
  btor_release_aig (amgr, and2);
  return cond;
}

void
btor_dump_aig (BtorAIGMgr *amgr, int binary, FILE *output, BtorAIG *aig)
{
  btor_dump_aigs (amgr, binary, output, 1, &aig, 0);
}

void
btor_dump_aigs (BtorAIGMgr *amgr,
                int binary,
                FILE *file,
                int naigs,
                BtorAIG **aigs,
                BtorPtrHashTable *backannotation)
{
  btor_dump_aiger (amgr, binary, file, naigs, aigs, 0, 0, 0, backannotation);
}

static unsigned
btor_aiger_encode_aig (BtorPtrHashTable *table, BtorAIG *aig)
{
  BtorPtrHashBucket *b;
  BtorAIG *real_aig;
  unsigned res;

  if (aig == BTOR_AIG_FALSE) return 0;

  if (aig == BTOR_AIG_TRUE) return 1;

  real_aig = BTOR_REAL_ADDR_AIG (aig);

  b = btor_find_in_ptr_hash_table (table, real_aig);
  assert (b);

  res = 2 * (unsigned) b->data.asInt;

  if (BTOR_IS_INVERTED_AIG (aig)) res ^= 1;

  return res;
}

void
btor_dump_aiger (BtorAIGMgr *amgr,
                 int binary,
                 FILE *file,
                 int naigs,
                 BtorAIG **aigs,
                 int nregs,
                 BtorAIG **regs,
                 BtorAIG **nexts,
                 BtorPtrHashTable *backannotation)
{
  unsigned aig_id, left_id, right_id, tmp, delta;
  BtorPtrHashTable *table, *latches;
  BtorAIG *aig, *left, *right;
  BtorPtrHashBucket *p, *b;
  int M, I, L, O, A, i, l;
  BtorAIGPtrStack stack;
  unsigned char ch;
  BtorMemMgr *mm;

  assert (naigs > 0);

  mm = amgr->mm;

  table   = btor_new_ptr_hash_table (amgr->mm, 0, 0);
  latches = btor_new_ptr_hash_table (amgr->mm, 0, 0);

  /* First add latches and inputs to hash tables.
   */
  for (i = nregs - 1; i >= 0; i--)
  {
    aig = regs[i];
    assert (!BTOR_IS_CONST_AIG (aig));
    assert (!btor_find_in_ptr_hash_table (latches, aig));
    btor_insert_in_ptr_hash_table (latches, aig);
  }

  BTOR_INIT_STACK (stack);
  for (i = naigs - 1; i >= 0; i--)
  {
    aig = aigs[i];
    if (!BTOR_IS_CONST_AIG (aig)) BTOR_PUSH_STACK (mm, stack, aig);
  }
  for (i = nregs - 1; i >= 0; i--)
  {
    aig = nexts[i];
    if (!BTOR_IS_CONST_AIG (aig)) BTOR_PUSH_STACK (mm, stack, aig);
  }

  M = 0;

  while (!BTOR_EMPTY_STACK (stack))
  {
    aig = BTOR_POP_STACK (stack);

  CONTINUE_WITHOUT_POP:

    assert (!BTOR_IS_CONST_AIG (aig));
    aig = BTOR_REAL_ADDR_AIG (aig);

    if (aig->mark) continue;

    aig->mark = 1;

    if (BTOR_IS_VAR_AIG (aig))
    {
      if (btor_find_in_ptr_hash_table (latches, aig)) continue;

      p             = btor_insert_in_ptr_hash_table (table, aig);
      p->data.asInt = ++M;
      assert (M > 0);
    }
    else
    {
      assert (BTOR_IS_AND_AIG (aig));

      right = BTOR_RIGHT_CHILD_AIG (aig);
      BTOR_PUSH_STACK (mm, stack, right);

      aig = BTOR_LEFT_CHILD_AIG (aig);
      goto CONTINUE_WITHOUT_POP;
    }
  }

  for (i = 0; i < nregs; i++)
  {
    aig = regs[i];
    assert (!BTOR_IS_CONST_AIG (aig));
    assert (btor_find_in_ptr_hash_table (latches, aig));
    assert (!btor_find_in_ptr_hash_table (table, aig));
    p             = btor_insert_in_ptr_hash_table (table, aig);
    p->data.asInt = ++M;
    assert (M > 0);
  }

  L = nregs;
  assert (L <= M);
  I = M - L;

  /* Then start adding AND gates in postfix order.
   */
  assert (BTOR_EMPTY_STACK (stack));
  for (i = nregs - 1; i >= 0; i--)
  {
    aig = nexts[i];
    if (!BTOR_IS_CONST_AIG (aig)) BTOR_PUSH_STACK (mm, stack, aig);
  }
  for (i = naigs - 1; i >= 0; i--)
  {
    aig = aigs[i];
    if (!BTOR_IS_CONST_AIG (aig)) BTOR_PUSH_STACK (mm, stack, aig);
  }

  while (!BTOR_EMPTY_STACK (stack))
  {
    aig = BTOR_POP_STACK (stack);

    if (aig)
    {
    CONTINUE_WITH_NON_ZERO_AIG:

      assert (!BTOR_IS_CONST_AIG (aig));
      aig = BTOR_REAL_ADDR_AIG (aig);

      if (!aig->mark) continue;

      aig->mark = 0;

      if (BTOR_IS_VAR_AIG (aig)) continue;

      BTOR_PUSH_STACK (mm, stack, aig);
      BTOR_PUSH_STACK (mm, stack, 0);

      right = BTOR_RIGHT_CHILD_AIG (aig);
      BTOR_PUSH_STACK (mm, stack, right);

      aig = BTOR_LEFT_CHILD_AIG (aig);
      goto CONTINUE_WITH_NON_ZERO_AIG;
    }
    else
    {
      assert (!BTOR_EMPTY_STACK (stack));

      aig = BTOR_POP_STACK (stack);
      assert (aig);
      assert (!aig->mark);

      assert (aig);
      assert (BTOR_REAL_ADDR_AIG (aig) == aig);
      assert (BTOR_IS_AND_AIG (aig));

      p             = btor_insert_in_ptr_hash_table (table, aig);
      p->data.asInt = ++M;
      assert (M > 0);
    }
  }

  A = M - I - L;

  BTOR_RELEASE_STACK (mm, stack);

  O = naigs;

  fprintf (file, "a%cg %d %d %d %d %d\n", binary ? 'i' : 'a', M, I, L, O, A);

  /* Only need to print inputs in non binary mode.
   */
  i = 0;
  for (p = table->first; p; p = p->next)
  {
    aig = p->key;

    assert (aig);
    assert (!BTOR_IS_INVERTED_AIG (aig));

    if (!BTOR_IS_VAR_AIG (aig)) break;

    if (btor_find_in_ptr_hash_table (latches, aig)) continue;

    if (!binary) fprintf (file, "%d\n", 2 * p->data.asInt);

    i++;
  }

  /* Now the latches aka regs.
   */
  for (i = 0; i < nregs; i++)
  {
    if (!binary) fprintf (file, "%u ", btor_aiger_encode_aig (table, regs[i]));

    fprintf (file, "%u\n", btor_aiger_encode_aig (table, nexts[i]));
  }

  /* Then the outputs ...
   */
  for (i = 0; i < naigs; i++)
    fprintf (file, "%u\n", btor_aiger_encode_aig (table, aigs[i]));

  /* And finally all the AND gates.
   */
  while (p)
  {
    aig = p->key;

    assert (aig);
    assert (!BTOR_IS_INVERTED_AIG (aig));
    assert (BTOR_IS_AND_AIG (aig));

    left  = BTOR_LEFT_CHILD_AIG (aig);
    right = BTOR_RIGHT_CHILD_AIG (aig);

    aig_id   = 2 * (unsigned) p->data.asInt;
    left_id  = btor_aiger_encode_aig (table, left);
    right_id = btor_aiger_encode_aig (table, right);

    if (left_id < right_id)
    {
      tmp      = left_id;
      left_id  = right_id;
      right_id = tmp;
    }

    assert (aig_id > left_id);
    assert (left_id >= right_id); /* strict ? */

    if (binary)
    {
      for (i = 0; i < 2; i++)
      {
        delta = i ? left_id - right_id : aig_id - left_id;
        tmp   = delta;

        while (tmp & ~0x7f)
        {
          ch = tmp & 0x7f;
          ch |= 0x80;

          putc (ch, file);
          tmp >>= 7;
        }

        ch = tmp;
        putc (ch, file);
      }
    }
    else
      fprintf (file, "%u %u %u\n", aig_id, left_id, right_id);

    p = p->next;
  }

  /* If we have back annotation add a symbol table.
   */
  i = l = 0;
  if (backannotation)
  {
    for (p = table->first; p; p = p->next)
    {
      aig = p->key;
      if (!BTOR_IS_VAR_AIG (aig)) break;

      b = btor_find_in_ptr_hash_table (backannotation, aig);

      if (!b) continue;

      assert (b->key == aig);
      assert (b->data.asStr);

      if (btor_find_in_ptr_hash_table (latches, aig))
      {
        assert (p->data.asInt == i + l + 1);
        fprintf (file, "l%d %s\n", l++, b->data.asStr);
      }
      else
      {
        assert (p->data.asInt == i + l + 1);
        fprintf (file, "i%d %s\n", i++, b->data.asStr);
      }
    }
  }

  btor_delete_ptr_hash_table (table);
  btor_delete_ptr_hash_table (latches);
}

BtorAIGMgr *
btor_new_aig_mgr (BtorMemMgr *mm, BtorMsg *msg)
{
  assert (mm);

  BtorAIGMgr *amgr;

  BTOR_CNEW (mm, amgr);
  amgr->mm  = mm;
  amgr->msg = msg;
  BTOR_INIT_AIG_UNIQUE_TABLE (mm, amgr->table);
  amgr->smgr = btor_new_sat_mgr (mm, amgr->msg);
  BTOR_INIT_STACK (amgr->id2aig);
  BTOR_PUSH_STACK (mm, amgr->id2aig, BTOR_AIG_FALSE);
  BTOR_PUSH_STACK (mm, amgr->id2aig, BTOR_AIG_TRUE);
  assert ((size_t) BTOR_AIG_FALSE == 0);
  assert ((size_t) BTOR_AIG_TRUE == 1);
  BTOR_INIT_STACK (amgr->cnfid2aig);
  return amgr;
}

static BtorAIG *
clone_aig (BtorMemMgr *mm, BtorAIG *aig)
{
  assert (mm);

  size_t size;
  BtorAIG *res, *real_aig;

  if (BTOR_IS_CONST_AIG (aig)) return aig;

  real_aig = BTOR_REAL_ADDR_AIG (aig);
  size     = sizeof (BtorAIG);
  if (!real_aig->is_var) size += 2 * sizeof (int32_t);
  res = btor_malloc (mm, size);
  memcpy (res, real_aig, size);

  res = BTOR_IS_INVERTED_AIG (aig) ? BTOR_INVERT_AIG (res) : res;
  return res;
}

static void
clone_aigs (BtorAIGMgr *amgr, BtorAIGMgr *clone)
{
  assert (amgr);
  assert (clone);

  int i;
  size_t size;
  BtorMemMgr *mm;
  BtorAIG *aig;

  mm = clone->mm;

  /* clone id2aig table */
  BTOR_INIT_STACK (clone->id2aig);
  size = BTOR_SIZE_STACK (amgr->id2aig);
  if (size)
  {
    BTOR_CNEWN (mm, clone->id2aig.start, size);
    clone->id2aig.end = clone->id2aig.start + size;
    clone->id2aig.top = clone->id2aig.start + BTOR_COUNT_STACK (amgr->id2aig);
  }
  for (i = 0; i < BTOR_COUNT_STACK (amgr->id2aig); i++)
  {
    aig = clone_aig (mm, BTOR_PEEK_STACK (amgr->id2aig, i));
    BTOR_POKE_STACK (clone->id2aig, i, aig);
  }

  /* clone unique table */
  BTOR_CNEWN (mm, clone->table.chains, amgr->table.size);
  clone->table.size         = amgr->table.size;
  clone->table.num_elements = amgr->table.num_elements;
  memcpy (clone->table.chains,
          amgr->table.chains,
          amgr->table.size * sizeof (int32_t));

  /* clone cnfid2aig table */
  BTOR_INIT_STACK (clone->cnfid2aig);
  size = BTOR_SIZE_STACK (amgr->cnfid2aig);
  if (size)
  {
    BTOR_CNEWN (mm, clone->cnfid2aig.start, size);
    clone->cnfid2aig.end = clone->cnfid2aig.start + size;
    clone->cnfid2aig.top = clone->cnfid2aig.start;
    memcpy (
        clone->cnfid2aig.start, amgr->cnfid2aig.start, size * sizeof (int32_t));
  }
  assert (BTOR_SIZE_STACK (clone->cnfid2aig)
          == BTOR_SIZE_STACK (amgr->cnfid2aig));
  assert (BTOR_COUNT_STACK (clone->cnfid2aig)
          == BTOR_COUNT_STACK (amgr->cnfid2aig));
}

BtorAIGMgr *
btor_clone_aig_mgr (BtorMemMgr *mm, BtorMsg *msg, BtorAIGMgr *amgr)
{
  assert (mm);
  assert (msg);
  assert (amgr);

  BtorAIGMgr *res;

  BTOR_CNEW (mm, res);
  res->mm  = mm;
  res->msg = msg;

  res->smgr = btor_clone_sat_mgr (mm, msg, amgr->smgr);
  /* Note: we do not yet clone aigs here (we need the clone of the aig
   *       manager for that). */
  res->max_num_aigs     = amgr->max_num_aigs;
  res->cur_num_aigs     = amgr->cur_num_aigs;
  res->cur_num_aig_vars = amgr->cur_num_aig_vars;
  res->num_vars         = amgr->num_vars;
  res->num_clauses      = amgr->num_clauses;
  clone_aigs (amgr, res);
  return res;
}

void
btor_delete_aig_mgr (BtorAIGMgr *amgr)
{
  BtorMemMgr *mm;
  assert (amgr);
  assert (getenv ("BTORLEAK") || getenv ("BTORLEAKAIG")
          || amgr->table.num_elements == 0);
  mm = amgr->mm;
  BTOR_RELEASE_AIG_UNIQUE_TABLE (mm, amgr->table);
  btor_delete_sat_mgr (amgr->smgr);
  BTOR_RELEASE_STACK (mm, amgr->id2aig);
  BTOR_RELEASE_STACK (mm, amgr->cnfid2aig);
  BTOR_DELETE (mm, amgr);
}

static int
btor_is_xor_aig (BtorAIGMgr *amgr, BtorAIG *aig, BtorAIGPtrStack *leafs)
{
  BtorAIG *l, *r, *ll, *lr, *rl, *rr;

  assert (BTOR_IS_AND_AIG (aig));
  assert (!BTOR_IS_INVERTED_AIG (aig));

  l = BTOR_LEFT_CHILD_AIG (aig);
  if (!BTOR_IS_INVERTED_AIG (l)) return 0;
  l = BTOR_REAL_ADDR_AIG (l);
  if (l->refs > 1) return 0;

  r = BTOR_RIGHT_CHILD_AIG (aig);
  if (!BTOR_IS_INVERTED_AIG (r)) return 0;
  r = BTOR_REAL_ADDR_AIG (r);
  if (r->refs > 1) return 0;

  ll = BTOR_LEFT_CHILD_AIG (l);
  lr = BTOR_RIGHT_CHILD_AIG (l);

  rl = BTOR_LEFT_CHILD_AIG (r);
  rr = BTOR_RIGHT_CHILD_AIG (r);

  if (ll == BTOR_INVERT_AIG (rl) && lr == BTOR_INVERT_AIG (rr))
  {
    BTOR_PUSH_STACK (amgr->mm, *leafs, rr);
    BTOR_PUSH_STACK (amgr->mm, *leafs, ll);
    return 1;
  }

  assert (ll != BTOR_INVERT_AIG (rr) || lr != BTOR_INVERT_AIG (rl));

  return 0;
}

static int
btor_is_ite_aig (BtorAIGMgr *amgr, BtorAIG *aig, BtorAIGPtrStack *leafs)
{
  BtorAIG *l, *r, *ll, *lr, *rl, *rr;

  assert (BTOR_IS_AND_AIG (aig));
  assert (!BTOR_IS_INVERTED_AIG (aig));

  l = BTOR_LEFT_CHILD_AIG (aig);
  if (!BTOR_IS_INVERTED_AIG (l)) return 0;
  l = BTOR_REAL_ADDR_AIG (l);
  if (l->refs > 1) return 0;

  r = BTOR_RIGHT_CHILD_AIG (aig);
  if (!BTOR_IS_INVERTED_AIG (r)) return 0;
  r = BTOR_REAL_ADDR_AIG (r);
  if (r->refs > 1) return 0;

  ll = BTOR_LEFT_CHILD_AIG (l);
  lr = BTOR_RIGHT_CHILD_AIG (l);

  rl = BTOR_LEFT_CHILD_AIG (r);
  rr = BTOR_RIGHT_CHILD_AIG (r);

  // aig == (!ll | !lr)(!rl | !rr)

  if (BTOR_INVERT_AIG (lr) == rl)
  {
    // aig == (!rl -> !ll)(rl -> !rr) = rl ? !rr : !ll
    BTOR_PUSH_STACK (amgr->mm, *leafs, BTOR_INVERT_AIG (ll));  // else
    BTOR_PUSH_STACK (amgr->mm, *leafs, BTOR_INVERT_AIG (rr));  // then
    BTOR_PUSH_STACK (amgr->mm, *leafs, rl);                    // cond
    return 1;
  }
  if (BTOR_INVERT_AIG (ll) == rl)
  {
    // aig == (!rl -> !lr)(rl -> !rr)
    BTOR_PUSH_STACK (amgr->mm, *leafs, BTOR_INVERT_AIG (lr));  // else
    BTOR_PUSH_STACK (amgr->mm, *leafs, BTOR_INVERT_AIG (rr));  // then
    BTOR_PUSH_STACK (amgr->mm, *leafs, rl);                    // cond
    return 1;
  }
  if (BTOR_INVERT_AIG (lr) == rr)
  {
    // aig == (!rr -> !ll)(rr -> !rl)
    BTOR_PUSH_STACK (amgr->mm, *leafs, BTOR_INVERT_AIG (ll));  // else
    BTOR_PUSH_STACK (amgr->mm, *leafs, BTOR_INVERT_AIG (rl));  // then
    BTOR_PUSH_STACK (amgr->mm, *leafs, rr);                    // cond
    return 1;
  }
  if (BTOR_INVERT_AIG (ll) == rr)
  {
    // aig == (!rr -> !lr)(rr -> !rl)
    BTOR_PUSH_STACK (amgr->mm, *leafs, BTOR_INVERT_AIG (lr));  // else
    BTOR_PUSH_STACK (amgr->mm, *leafs, BTOR_INVERT_AIG (rl));  // then
    BTOR_PUSH_STACK (amgr->mm, *leafs, rr);                    // cond
    return 1;
  }

  return 0;
}

static void
btor_set_next_id_aig_mgr (BtorAIGMgr *amgr, BtorAIG *root)
{
  assert (!BTOR_IS_INVERTED_AIG (root));
  assert (!root->cnf_id);
  root->cnf_id = btor_next_cnf_id_sat_mgr (amgr->smgr);
  assert (root->cnf_id > 0);
  BTOR_FIT_STACK (amgr->mm, amgr->cnfid2aig, (size_t) root->cnf_id);
  amgr->cnfid2aig.start[root->cnf_id] = root->id;
  assert (amgr->cnfid2aig.start[root->cnf_id] == root->id);
  amgr->num_vars++;
}

#ifdef BTOR_EXTRACT_TOP_LEVEL_MULTI_OR
static int
btor_is_or_aig (BtorAIGMgr *amgr, BtorAIG *root, BtorAIGPtrStack *leafs)
{
  assert (amgr);
  assert (root);
  assert (leafs);
  assert (BTOR_EMPTY_STACK (*leafs));

  BtorAIG *real_cur, *cur, **p;
  BtorAIGPtrStack tree;
  BtorMemMgr *mm;

  if (!BTOR_IS_INVERTED_AIG (root)
      || !BTOR_IS_AND_AIG (BTOR_REAL_ADDR_AIG (root)))
    return 0;

  mm   = amgr->mm;
  root = BTOR_REAL_ADDR_AIG (root);

  BTOR_INIT_STACK (tree);
  BTOR_PUSH_STACK (mm, tree, BTOR_RIGHT_CHILD_AIG (root));
  BTOR_PUSH_STACK (mm, tree, BTOR_LEFT_CHILD_AIG (root));

  while (!BTOR_EMPTY_STACK (tree))
  {
    cur      = BTOR_POP_STACK (tree);
    real_cur = BTOR_REAL_ADDR_AIG (cur);

    if (BTOR_IS_CONST_AIG (real_cur))
    {
      assert (cur == BTOR_AIG_FALSE);
      continue;
    }

    if (real_cur->mark) continue;

    if (!BTOR_IS_INVERTED_AIG (cur) && BTOR_IS_AND_AIG (real_cur))
    {
      BTOR_PUSH_STACK (mm, tree, BTOR_RIGHT_CHILD_AIG (real_cur));
      BTOR_PUSH_STACK (mm, tree, BTOR_LEFT_CHILD_AIG (real_cur));
    }
    else
    {
      BTOR_PUSH_STACK (mm, *leafs, cur);
      real_cur->mark = 1;
    }
  }

  for (p = (*leafs).start; p < (*leafs).top; p++)
  {
    cur = *p;
    assert (BTOR_REAL_ADDR_AIG (cur)->mark);
    BTOR_REAL_ADDR_AIG (cur)->mark = 0;
  }

  BTOR_RELEASE_STACK (mm, tree);
  return 1;
}
#endif

void
btor_aig_to_sat_tseitin (BtorAIGMgr *amgr, BtorAIG *start)
{
  BtorAIGPtrStack stack, tree, leafs, marked;
  int x, y, isxor, isite, a, b, c;
  BtorAIG *root, *cur;
  BtorSATMgr *smgr;
  BtorMemMgr *mm;
  unsigned local;
  BtorAIG **p;

  if (BTOR_IS_CONST_AIG (start)) return;

  BTOR_INIT_STACK (stack);
  BTOR_INIT_STACK (tree);
  BTOR_INIT_STACK (leafs);
  BTOR_INIT_STACK (marked);

  assert (amgr);

  smgr = amgr->smgr;
  mm   = amgr->mm;

  start = BTOR_REAL_ADDR_AIG (start);
  BTOR_PUSH_STACK (mm, stack, start);

  while (!BTOR_EMPTY_STACK (stack))
  {
    root = BTOR_REAL_ADDR_AIG (BTOR_POP_STACK (stack));

    if (root->mark == 2)
    {
      assert (root->cnf_id);
      assert (root->local < root->refs);
      root->local++;
      continue;
    }

    if (root->cnf_id) continue;

    if (BTOR_IS_VAR_AIG (root))
    {
      btor_set_next_id_aig_mgr (amgr, root);
      continue;
    }

    assert (root->mark < 2);
    assert (BTOR_IS_AND_AIG (root));
    assert (BTOR_EMPTY_STACK (tree));
    assert (BTOR_EMPTY_STACK (leafs));

    if ((isxor = btor_is_xor_aig (amgr, root, &leafs)))
      isite = 0;
    else
      isite = btor_is_ite_aig (amgr, root, &leafs);

    if (!isxor && !isite)
    {
      BTOR_PUSH_STACK (mm, tree, BTOR_RIGHT_CHILD_AIG (root));
      BTOR_PUSH_STACK (mm, tree, BTOR_LEFT_CHILD_AIG (root));

      while (!BTOR_EMPTY_STACK (tree))
      {
        cur = BTOR_POP_STACK (tree);

        if (BTOR_IS_INVERTED_AIG (cur) || BTOR_IS_VAR_AIG (cur)
            || cur->refs > 1u || cur->cnf_id)
        {
          BTOR_PUSH_STACK (mm, leafs, cur);
        }
        else
        {
          BTOR_PUSH_STACK (mm, tree, BTOR_RIGHT_CHILD_AIG (cur));
          BTOR_PUSH_STACK (mm, tree, BTOR_LEFT_CHILD_AIG (cur));
        }
      }
    }

    if (root->mark == 0)
    {
      root->mark = 1;
      assert (root->refs >= 1);
      assert (!root->local);
      root->local = 1;
      BTOR_PUSH_STACK (mm, marked, root);
      BTOR_PUSH_STACK (mm, stack, root);
      for (p = leafs.start; p < leafs.top; p++) BTOR_PUSH_STACK (mm, stack, *p);
    }
    else
    {
      assert (root->mark == 1);
      root->mark = 2;

      btor_set_next_id_aig_mgr (amgr, root);
      x = root->cnf_id;
      assert (x);

      if (isxor)
      {
        assert (BTOR_COUNT_STACK (leafs) == 2);
        a = BTOR_GET_CNF_ID_AIG (leafs.start[0]);
        b = BTOR_GET_CNF_ID_AIG (leafs.start[1]);

        btor_add_sat (smgr, -x);
        btor_add_sat (smgr, a);
        btor_add_sat (smgr, -b);
        btor_add_sat (smgr, 0);

        btor_add_sat (smgr, -x);
        btor_add_sat (smgr, -a);
        btor_add_sat (smgr, b);
        btor_add_sat (smgr, 0);

        btor_add_sat (smgr, x);
        btor_add_sat (smgr, -a);
        btor_add_sat (smgr, -b);
        btor_add_sat (smgr, 0);

        btor_add_sat (smgr, x);
        btor_add_sat (smgr, a);
        btor_add_sat (smgr, b);
        btor_add_sat (smgr, 0);
        amgr->num_clauses += 4;
        amgr->num_literals += 12;
      }
      else if (isite)
      {
        assert (BTOR_COUNT_STACK (leafs) == 3);
        a = BTOR_GET_CNF_ID_AIG (leafs.start[0]);  // else
        b = BTOR_GET_CNF_ID_AIG (leafs.start[1]);  // then
        c = BTOR_GET_CNF_ID_AIG (leafs.start[2]);  // cond

        btor_add_sat (smgr, -x);
        btor_add_sat (smgr, -c);
        btor_add_sat (smgr, b);
        btor_add_sat (smgr, 0);

        btor_add_sat (smgr, -x);
        btor_add_sat (smgr, c);
        btor_add_sat (smgr, a);
        btor_add_sat (smgr, 0);

        btor_add_sat (smgr, x);
        btor_add_sat (smgr, -c);
        btor_add_sat (smgr, -b);
        btor_add_sat (smgr, 0);

        btor_add_sat (smgr, x);
        btor_add_sat (smgr, c);
        btor_add_sat (smgr, -a);
        btor_add_sat (smgr, 0);
        amgr->num_clauses += 4;
        amgr->num_literals += 12;
      }
      else
      {
        for (p = leafs.start; p < leafs.top; p++)
        {
          cur = *p;
          y   = BTOR_GET_CNF_ID_AIG (cur);
          assert (y);
          btor_add_sat (smgr, -y);
          amgr->num_literals++;
        }
        btor_add_sat (smgr, x);
        btor_add_sat (smgr, 0);
        amgr->num_clauses++;
        amgr->num_literals++;

        for (p = leafs.start; p < leafs.top; p++)
        {
          cur = *p;
          y   = BTOR_GET_CNF_ID_AIG (cur);
          btor_add_sat (smgr, -x);
          btor_add_sat (smgr, y);
          btor_add_sat (smgr, 0);
          amgr->num_clauses++;
          amgr->num_literals += 2;
        }
      }
    }
    BTOR_RESET_STACK (leafs);
  }
  BTOR_RELEASE_STACK (mm, stack);
  BTOR_RELEASE_STACK (mm, leafs);
  BTOR_RELEASE_STACK (mm, tree);

  while (!BTOR_EMPTY_STACK (marked))
  {
    cur = BTOR_POP_STACK (marked);
    assert (!BTOR_IS_INVERTED_AIG (cur));
    assert (cur->mark > 0);
    cur->mark = 0;
    assert (cur->cnf_id);
    assert (BTOR_IS_AND_AIG (cur));
    local = cur->local;
    assert (local > 0);
    cur->local = 0;
    if (cur == start) continue;
    assert (cur->refs >= local);
    if (cur->refs > local) continue;
    btor_release_cnf_id_aig_mgr (amgr, cur);
  }
  BTOR_RELEASE_STACK (mm, marked);
}

static void
aig_to_sat_tseitin (BtorAIGMgr *amgr, BtorAIG *aig)
{
  assert (amgr);
  assert (!BTOR_IS_CONST_AIG (aig));
  BTOR_MSG (
      amgr->msg, 3, "transforming AIG into CNF using Tseitin transformation");
  btor_aig_to_sat_tseitin (amgr, aig);
}

void
btor_aig_to_sat (BtorAIGMgr *amgr, BtorAIG *aig)
{
  assert (amgr);
  if (!BTOR_IS_CONST_AIG (aig)) aig_to_sat_tseitin (amgr, aig);
}

void
btor_add_toplevel_aig_to_sat (BtorAIGMgr *amgr, BtorAIG *root)
{
  BtorMemMgr *mm;
  BtorSATMgr *smgr;
  BtorAIG *aig, *real_aig, *left, *right;
  BtorAIGPtrStack stack;
#ifdef BTOR_EXTRACT_TOP_LEVEL_MULTI_OR
  BtorAIGPtrStack leafs;
  BtorAig **p;
#endif

  mm   = amgr->mm;
  smgr = amgr->smgr;

  if (root == BTOR_AIG_TRUE) return;

  if (root == BTOR_AIG_FALSE)
  {
    btor_add_sat (smgr, 0); /* add empty clause */
    amgr->num_clauses++;
    return;
  }

  BTOR_INIT_STACK (stack);
  aig = root;
  goto BTOR_ADD_TOPLEVEL_AIG_TO_SAT_WITHOUT_POP;

  while (!BTOR_EMPTY_STACK (stack))
  {
    aig = BTOR_POP_STACK (stack);
  BTOR_ADD_TOPLEVEL_AIG_TO_SAT_WITHOUT_POP:
    if (!BTOR_IS_INVERTED_AIG (aig) && BTOR_IS_AND_AIG (aig))
    {
      BTOR_PUSH_STACK (mm, stack, BTOR_RIGHT_CHILD_AIG (aig));
      BTOR_PUSH_STACK (mm, stack, BTOR_LEFT_CHILD_AIG (aig));
    }
    else
    {
      real_aig = BTOR_REAL_ADDR_AIG (aig);

#ifdef BTOR_EXTRACT_TOP_LEVEL_MULTI_OR
      BTOR_INIT_STACK (leafs);
      if (btor_is_or_aig (amgr, aig, &leafs))
      {
        assert (BTOR_COUNT_STACK (leafs) > 1);
        for (p = leafs.start; p < leafs.top; p++)
        {
          left = *p;
          if (BTOR_IS_CONST_AIG (left)) continue;
          btor_aig_to_sat (amgr, left);
        }
        for (p = leafs.start; p < leafs.top; p++)
        {
          left = *p;
          assert (BTOR_GET_CNF_ID_AIG (left));
          btor_add_sat (smgr, BTOR_GET_CNF_ID_AIG (BTOR_INVERT_AIG (left)));
          amgr->num_literals++;
        }
        btor_add_sat (smgr, 0);
        amgr->num_clauses++;
      }
      else
      {
        btor_aig_to_sat (amgr, aig);
        btor_add_sat (smgr, BTOR_GET_CNF_ID_AIG (aig));
        btor_add_sat (smgr, 0);
        amgr->num_literals++;
        amgr->num_clauses++;
      }
      BTOR_RELEASE_STACK (mm, leafs);
#else
      if (BTOR_IS_INVERTED_AIG (aig) && BTOR_IS_AND_AIG (real_aig))
      {
        left  = BTOR_INVERT_AIG (BTOR_LEFT_CHILD_AIG (real_aig));
        right = BTOR_INVERT_AIG (BTOR_RIGHT_CHILD_AIG (real_aig));
        btor_aig_to_sat (amgr, left);
        btor_aig_to_sat (amgr, right);
        btor_add_sat (smgr, BTOR_GET_CNF_ID_AIG (left));
        btor_add_sat (smgr, BTOR_GET_CNF_ID_AIG (right));
        btor_add_sat (smgr, 0);
        amgr->num_clauses++;
        amgr->num_literals += 2;
      }
      else
      {
        btor_aig_to_sat (amgr, aig);
        btor_add_sat (smgr, BTOR_GET_CNF_ID_AIG (aig));
        btor_add_sat (smgr, 0);
        amgr->num_clauses++;
        amgr->num_literals++;
      }
#endif
    }
  }
  BTOR_RELEASE_STACK (mm, stack);
}

BtorSATMgr *
btor_get_sat_mgr_aig_mgr (const BtorAIGMgr *amgr)
{
  return amgr ? amgr->smgr : 0;
}

int
btor_get_assignment_aig (BtorAIGMgr *amgr, BtorAIG *aig)
{
  assert (amgr);
  if (aig == BTOR_AIG_TRUE) return 1;
  if (aig == BTOR_AIG_FALSE) return -1;
  if (BTOR_REAL_ADDR_AIG (aig)->cnf_id == 0) return 0;
  if (BTOR_IS_INVERTED_AIG (aig))
    return -btor_deref_sat (amgr->smgr, BTOR_REAL_ADDR_AIG (aig)->cnf_id);
  return btor_deref_sat (amgr->smgr, aig->cnf_id);
}

int
btor_cmp_aig (BtorAIG *a, BtorAIG *b)
{
  if (a == b) return 0;
  if (BTOR_INVERT_AIG (a) == b) return BTOR_IS_INVERTED_AIG (a) ? -1 : 1;
  if (BTOR_IS_INVERTED_AIG (a)) a = BTOR_INVERT_AIG (a);
  if (a == BTOR_AIG_FALSE) return -1;
  assert (a != BTOR_AIG_TRUE);
  if (BTOR_IS_INVERTED_AIG (b)) b = BTOR_INVERT_AIG (b);
  if (b == BTOR_AIG_FALSE) return 1;
  assert (b != BTOR_AIG_TRUE);
  return a->id - b->id;
}
