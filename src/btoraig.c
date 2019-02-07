/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2016 Armin Biere.
 *  Copyright (C) 2013-2017 Aina Niemetz.
 *  Copyright (C) 2013-2016 Mathias Preiner.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btoraig.h"

#include "btorabort.h"
#include "btorcore.h"
#include "btorsat.h"
#include "utils/btoraigmap.h"
#include "utils/btorhashptr.h"
#include "utils/btorutil.h"

#include <assert.h>
#include <limits.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>

/*------------------------------------------------------------------------*/

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

/*------------------------------------------------------------------------*/

//#define BTOR_EXTRACT_TOP_LEVEL_MULTI_OR

//#define BTOR_AIG_TO_CNF_TOP_ELIM

#define BTOR_AIG_TO_CNF_EXTRACT_ONLY_NON_SHARED

#define BTOR_AIG_TO_CNF_EXTRACT_ITE

#define BTOR_AIG_TO_CNF_EXTRACT_XOR

// #define BTOR_AIG_TO_CNF_NARY_AND

/*------------------------------------------------------------------------*/

static void
setup_aig_and_add_to_id_table (BtorAIGMgr *amgr, BtorAIG *aig)
{
  int32_t id;

  id = BTOR_COUNT_STACK (amgr->id2aig);
  BTOR_ABORT (id == INT32_MAX, "AIG id overflow");
  aig->refs = 1;
  aig->id   = id;
  BTOR_PUSH_STACK (amgr->id2aig, aig);
  assert (aig->id >= 0);
  assert (BTOR_COUNT_STACK (amgr->id2aig) == (size_t) aig->id + 1);
  assert (BTOR_PEEK_STACK (amgr->id2aig, aig->id) == aig);
}

static BtorAIG *
new_and_aig (BtorAIGMgr *amgr, BtorAIG *left, BtorAIG *right)
{
  assert (amgr);
  assert (!btor_aig_is_const (left));
  assert (!btor_aig_is_const (right));

  BtorAIG *aig;
  size_t size;

  size = sizeof (BtorAIG) + 2 * sizeof (int32_t);
  aig  = btor_mem_malloc (amgr->btor->mm, size);
  memset (aig, 0, size);
  setup_aig_and_add_to_id_table (amgr, aig);
  aig->children[0] = btor_aig_get_id (left);
  aig->children[1] = btor_aig_get_id (right);
  amgr->cur_num_aigs++;
  if (amgr->max_num_aigs < amgr->cur_num_aigs)
    amgr->max_num_aigs = amgr->cur_num_aigs;
  return aig;
}

static void
release_cnf_id_aig_mgr (BtorAIGMgr *amgr, BtorAIG *aig)
{
  assert (!BTOR_IS_INVERTED_AIG (aig));
  assert (aig->cnf_id > 0);
  assert ((size_t) aig->cnf_id < BTOR_SIZE_STACK (amgr->cnfid2aig));
  assert (amgr->cnfid2aig.start[aig->cnf_id] == aig->id);
  amgr->cnfid2aig.start[aig->cnf_id] = 0;
  btor_sat_mgr_release_cnf_id (amgr->smgr, aig->cnf_id);
  aig->cnf_id = 0;
}

static void
delete_aig_node (BtorAIGMgr *amgr, BtorAIG *aig)
{
  assert (!BTOR_IS_INVERTED_AIG (aig));
  assert (amgr);
  if (btor_aig_is_const (aig)) return;
  if (aig->cnf_id) release_cnf_id_aig_mgr (amgr, aig);
  amgr->id2aig.start[aig->id] = 0;
  if (aig->is_var)
  {
    amgr->cur_num_aig_vars--;
    BTOR_DELETE (amgr->btor->mm, aig);
  }
  else
  {
    amgr->cur_num_aigs--;
    btor_mem_free (
        amgr->btor->mm, aig, sizeof (BtorAIG) + 2 * sizeof (int32_t));
  }
}

static uint32_t
hash_aig (int32_t id0, int32_t id1, uint32_t table_size)
{
  uint32_t hash;
  assert (table_size > 0);
  assert (btor_util_is_power_of_2 (table_size));
  hash = 547789289u * (uint32_t) abs (id0);
  hash += 786695309u * (uint32_t) abs (id1);
  hash *= BTOR_AIG_UNIQUE_TABLE_PRIME;
  hash &= table_size - 1;
  return hash;
}

static uint32_t
compute_aig_hash (BtorAIG *aig, uint32_t table_size)
{
  uint32_t hash;
  assert (!BTOR_IS_INVERTED_AIG (aig));
  assert (btor_aig_is_and (aig));
  hash = hash_aig (aig->children[0], aig->children[1], table_size);
  return hash;
}

static void
delete_aig_nodes_unique_table_entry (BtorAIGMgr *amgr, BtorAIG *aig)
{
  uint32_t hash;
  BtorAIG *cur, *prev;
  assert (amgr);
  assert (!BTOR_IS_INVERTED_AIG (aig));
  assert (btor_aig_is_and (aig));
  prev = 0;
  hash = compute_aig_hash (aig, amgr->table.size);
  cur  = btor_aig_get_by_id (amgr, amgr->table.chains[hash]);
  while (cur != aig)
  {
    assert (!BTOR_IS_INVERTED_AIG (cur));
    prev = cur;
    cur  = btor_aig_get_by_id (amgr, cur->next);
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
  if (!btor_aig_is_const (aig))
  {
    BTOR_ABORT (BTOR_REAL_ADDR_AIG (aig)->refs == UINT32_MAX,
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
  assert (amgr);
  assert (!btor_aig_is_const (left));
  assert (!btor_aig_is_const (right));

  BtorAIG *cur;
  uint32_t hash;
  int32_t *result;

  if (btor_opt_get (amgr->btor, BTOR_OPT_SORT_AIG) > 0
      && BTOR_REAL_ADDR_AIG (right)->id < BTOR_REAL_ADDR_AIG (left)->id)
  {
    BTOR_SWAP (BtorAIG *, left, right);
  }

  hash   = hash_aig (BTOR_REAL_ADDR_AIG (left)->id,
                   BTOR_REAL_ADDR_AIG (right)->id,
                   amgr->table.size);
  result = amgr->table.chains + hash;
  cur    = btor_aig_get_by_id (amgr, *result);
  while (cur)
  {
    assert (!BTOR_IS_INVERTED_AIG (cur));
    assert (btor_aig_is_and (cur));
    if (btor_aig_get_left_child (amgr, cur) == left
        && btor_aig_get_right_child (amgr, cur) == right)
      break;
#ifndef NDEBUG
    if (btor_opt_get (amgr->btor, BTOR_OPT_SORT_AIG) > 0)
      assert (btor_aig_get_left_child (amgr, cur) != right
              || btor_aig_get_right_child (amgr, cur) != left);
#endif
    result = &cur->next;
    cur    = cur->next == 0 ? 0 : btor_aig_get_by_id (amgr, cur->next);
  }
  return result;
}

static BtorAIG *
find_and_aig_node (BtorAIGMgr *amgr, BtorAIG *left, BtorAIG *right)
{
  int32_t *lookup;
  BtorAIG *res;
  lookup = find_and_aig (amgr, left, right);
  assert (lookup);
  res = *lookup ? btor_aig_get_by_id (amgr, *lookup) : 0;
  return res;
}

static void
enlarge_aig_nodes_unique_table (BtorAIGMgr *amgr)
{
  BtorMemMgr *mm;
  int32_t *new_chains;
  uint32_t i, size, new_size;
  uint32_t hash;
  BtorAIG *temp = 0;
  BtorAIG *cur  = 0;
  assert (amgr);
  size     = amgr->table.size;
  new_size = size << 1;
  assert (new_size / size == 2);
  mm = amgr->btor->mm;
  BTOR_CNEWN (mm, new_chains, new_size);
  for (i = 0; i < size; i++)
  {
    cur = btor_aig_get_by_id (amgr, amgr->table.chains[i]);
    while (cur)
    {
      assert (!BTOR_IS_INVERTED_AIG (cur));
      assert (btor_aig_is_and (cur));
      temp             = btor_aig_get_by_id (amgr, cur->next);
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
btor_aig_copy (BtorAIGMgr *amgr, BtorAIG *aig)
{
  assert (amgr);
  (void) amgr;
  if (btor_aig_is_const (aig)) return aig;
  return inc_aig_ref_counter_and_return (aig);
}

void
btor_aig_release (BtorAIGMgr *amgr, BtorAIG *aig)
{
  BtorAIG *cur, *l, *r;
  BtorAIGPtrStack stack;
  BtorMemMgr *mm;

  assert (amgr);
  mm = amgr->btor->mm;

  if (!btor_aig_is_const (aig))
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
      BTOR_INIT_STACK (mm, stack);
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
          if (!btor_aig_is_var (cur))
          {
            assert (btor_aig_is_and (cur));
            l = btor_aig_get_left_child (amgr, cur);
            r = btor_aig_get_right_child (amgr, cur);
            BTOR_PUSH_STACK (stack, r);
            BTOR_PUSH_STACK (stack, l);
            delete_aig_nodes_unique_table_entry (amgr, cur);
          }

          delete_aig_node (amgr, cur);
        }
      }
      BTOR_RELEASE_STACK (stack);
    }
  }
}

BtorAIG *
btor_aig_var (BtorAIGMgr *amgr)
{
  BtorAIG *aig;
  assert (amgr);
  BTOR_CNEW (amgr->btor->mm, aig);
  setup_aig_and_add_to_id_table (amgr, aig);
  aig->is_var = 1;
  amgr->cur_num_aig_vars++;
  if (amgr->max_num_aig_vars < amgr->cur_num_aig_vars)
    amgr->max_num_aig_vars = amgr->cur_num_aig_vars;
  return aig;
}

BtorAIG *
btor_aig_not (BtorAIGMgr *amgr, BtorAIG *aig)
{
  assert (amgr);
  (void) amgr;
  inc_aig_ref_counter (aig);
  return BTOR_INVERT_AIG (aig);
}

static bool
find_and_contradiction_aig (
    BtorAIGMgr *amgr, BtorAIG *aig, BtorAIG *a0, BtorAIG *a1, uint32_t *calls)
{
  assert (amgr);
  assert (aig);
  assert (a0);
  assert (a1);
  assert (calls);
  (void) amgr;

  if (*calls >= BTOR_FIND_AND_AIG_CONTRADICTION_LIMIT) return false;

  if (!BTOR_IS_INVERTED_AIG (aig) && btor_aig_is_and (aig))
  {
    if (btor_aig_get_left_child (amgr, aig) == BTOR_INVERT_AIG (a0)
        || btor_aig_get_left_child (amgr, aig) == BTOR_INVERT_AIG (a1)
        || btor_aig_get_right_child (amgr, aig) == BTOR_INVERT_AIG (a0)
        || btor_aig_get_right_child (amgr, aig) == BTOR_INVERT_AIG (a1))
      return true;
    *calls += 1;
    return find_and_contradiction_aig (
               amgr, btor_aig_get_left_child (amgr, aig), a0, a1, calls)
           || find_and_contradiction_aig (
                  amgr, btor_aig_get_right_child (amgr, aig), a0, a1, calls);
  }
  return false;
}

static BtorAIG *
simp_aig_by_sat (BtorAIGMgr *amgr, BtorAIG *aig)
{
  int32_t lit, val, repr, sign;
  BtorAIG *res;

  /* fixed handling for const aigs not supported by minisat
   * (returns 0) FIXME why? */
  if (btor_aig_is_const (aig)) return aig;

  lit = btor_aig_get_cnf_id (aig);
  if (!lit) return aig;
  val = btor_sat_fixed (amgr->smgr, lit);
  if (val) return (val < 0) ? BTOR_AIG_FALSE : BTOR_AIG_TRUE;
  repr = btor_sat_repr (amgr->smgr, lit);
  if ((sign = (repr < 0))) repr = -repr;
  assert (repr >= 0);
  assert ((size_t) repr < BTOR_SIZE_STACK (amgr->cnfid2aig));
  res = btor_aig_get_by_id (amgr, amgr->cnfid2aig.start[repr]);
  if (!res) return aig;
  if (sign) res = BTOR_INVERT_AIG (res);
  return res;
}

BtorAIG *
btor_aig_and (BtorAIGMgr *amgr, BtorAIG *left, BtorAIG *right)
{
  BtorAIG *res, *real_left, *real_right;
  int32_t *lookup;
  uint32_t calls;

  assert (amgr);

  if (amgr->smgr->initialized)
  {
    left  = simp_aig_by_sat (amgr, left);
    right = simp_aig_by_sat (amgr, right);
  }

  calls = 0;

BTOR_AIG_TWO_LEVEL_OPT_TRY_AGAIN:
  if (left == BTOR_AIG_FALSE || right == BTOR_AIG_FALSE) return BTOR_AIG_FALSE;

  if (left == BTOR_AIG_TRUE) return inc_aig_ref_counter_and_return (right);

  if (right == BTOR_AIG_TRUE || (left == right))
    return inc_aig_ref_counter_and_return (left);
  if (left == BTOR_INVERT_AIG (right)) return BTOR_AIG_FALSE;

  real_left  = BTOR_REAL_ADDR_AIG (left);
  real_right = BTOR_REAL_ADDR_AIG (right);

  /* 2 level minimization rules for AIGs */
  /* first rule of contradiction */
  if (btor_aig_is_and (real_left) && !BTOR_IS_INVERTED_AIG (left))
  {
    if (btor_aig_get_left_child (amgr, real_left) == BTOR_INVERT_AIG (right)
        || btor_aig_get_right_child (amgr, real_left)
               == BTOR_INVERT_AIG (right))
      return BTOR_AIG_FALSE;
  }
  /* use commutativity */
  if (btor_aig_is_and (real_right) && !BTOR_IS_INVERTED_AIG (right))
  {
    if (btor_aig_get_left_child (amgr, real_right) == BTOR_INVERT_AIG (left)
        || btor_aig_get_right_child (amgr, real_right)
               == BTOR_INVERT_AIG (left))
      return BTOR_AIG_FALSE;
  }
  /* second rule of contradiction */
  if (btor_aig_is_and (real_right) && btor_aig_is_and (real_left)
      && !BTOR_IS_INVERTED_AIG (left) && !BTOR_IS_INVERTED_AIG (right))
  {
    if (btor_aig_get_left_child (amgr, real_left)
            == BTOR_INVERT_AIG (btor_aig_get_left_child (amgr, real_right))
        || btor_aig_get_left_child (amgr, real_left)
               == BTOR_INVERT_AIG (btor_aig_get_right_child (amgr, real_right))
        || btor_aig_get_right_child (amgr, real_left)
               == BTOR_INVERT_AIG (btor_aig_get_left_child (amgr, real_right))
        || btor_aig_get_right_child (amgr, real_left)
               == BTOR_INVERT_AIG (btor_aig_get_right_child (amgr, real_right)))
      return BTOR_AIG_FALSE;
  }
  /* first rule of subsumption */
  if (btor_aig_is_and (real_left) && BTOR_IS_INVERTED_AIG (left))
  {
    if (btor_aig_get_left_child (amgr, real_left) == BTOR_INVERT_AIG (right)
        || btor_aig_get_right_child (amgr, real_left)
               == BTOR_INVERT_AIG (right))
      return inc_aig_ref_counter_and_return (right);
  }
  /* use commutativity */
  if (btor_aig_is_and (real_right) && BTOR_IS_INVERTED_AIG (right))
  {
    if (btor_aig_get_left_child (amgr, real_right) == BTOR_INVERT_AIG (left)
        || btor_aig_get_right_child (amgr, real_right)
               == BTOR_INVERT_AIG (left))
      return inc_aig_ref_counter_and_return (left);
  }
  /* second rule of subsumption */
  if (btor_aig_is_and (real_right) && btor_aig_is_and (real_left)
      && BTOR_IS_INVERTED_AIG (left) && !BTOR_IS_INVERTED_AIG (right))
  {
    if (btor_aig_get_left_child (amgr, real_left)
            == BTOR_INVERT_AIG (btor_aig_get_left_child (amgr, real_right))
        || btor_aig_get_left_child (amgr, real_left)
               == BTOR_INVERT_AIG (btor_aig_get_right_child (amgr, real_right))
        || btor_aig_get_right_child (amgr, real_left)
               == BTOR_INVERT_AIG (btor_aig_get_left_child (amgr, real_right))
        || btor_aig_get_right_child (amgr, real_left)
               == BTOR_INVERT_AIG (btor_aig_get_right_child (amgr, real_right)))
      return inc_aig_ref_counter_and_return (right);
  }
  /* use commutativity */
  if (btor_aig_is_and (real_right) && btor_aig_is_and (real_left)
      && !BTOR_IS_INVERTED_AIG (left) && BTOR_IS_INVERTED_AIG (right))
  {
    if (btor_aig_get_left_child (amgr, real_left)
            == BTOR_INVERT_AIG (btor_aig_get_left_child (amgr, real_right))
        || btor_aig_get_left_child (amgr, real_left)
               == BTOR_INVERT_AIG (btor_aig_get_right_child (amgr, real_right))
        || btor_aig_get_right_child (amgr, real_left)
               == BTOR_INVERT_AIG (btor_aig_get_left_child (amgr, real_right))
        || btor_aig_get_right_child (amgr, real_left)
               == BTOR_INVERT_AIG (btor_aig_get_right_child (amgr, real_right)))
      return inc_aig_ref_counter_and_return (left);
  }
  /* rule of resolution */
  if (btor_aig_is_and (real_right) && btor_aig_is_and (real_left)
      && BTOR_IS_INVERTED_AIG (left) && BTOR_IS_INVERTED_AIG (right))
  {
    if ((btor_aig_get_left_child (amgr, real_left)
             == btor_aig_get_left_child (amgr, real_right)
         && btor_aig_get_right_child (amgr, real_left)
                == BTOR_INVERT_AIG (
                       btor_aig_get_right_child (amgr, real_right)))
        || (btor_aig_get_left_child (amgr, real_left)
                == btor_aig_get_right_child (amgr, real_right)
            && btor_aig_get_right_child (amgr, real_left)
                   == BTOR_INVERT_AIG (
                          btor_aig_get_left_child (amgr, real_right))))
      return inc_aig_ref_counter_and_return (
          BTOR_INVERT_AIG (btor_aig_get_left_child (amgr, real_left)));
  }
  /* use commutativity */
  if (btor_aig_is_and (real_right) && btor_aig_is_and (real_left)
      && BTOR_IS_INVERTED_AIG (left) && BTOR_IS_INVERTED_AIG (right))
  {
    if ((btor_aig_get_right_child (amgr, real_right)
             == btor_aig_get_right_child (amgr, real_left)
         && btor_aig_get_left_child (amgr, real_right)
                == BTOR_INVERT_AIG (btor_aig_get_left_child (amgr, real_left)))
        || (btor_aig_get_right_child (amgr, real_right)
                == btor_aig_get_left_child (amgr, real_left)
            && btor_aig_get_left_child (amgr, real_right)
                   == BTOR_INVERT_AIG (
                          btor_aig_get_right_child (amgr, real_left))))
      return inc_aig_ref_counter_and_return (
          BTOR_INVERT_AIG (btor_aig_get_right_child (amgr, real_right)));
  }
  /* asymmetric rule of idempotency */
  if (btor_aig_is_and (real_left) && !BTOR_IS_INVERTED_AIG (left))
  {
    if (btor_aig_get_left_child (amgr, real_left) == right
        || btor_aig_get_right_child (amgr, real_left) == right)
      return inc_aig_ref_counter_and_return (left);
  }
  /* use commutativity */
  if (btor_aig_is_and (real_right) && !BTOR_IS_INVERTED_AIG (right))
  {
    if (btor_aig_get_left_child (amgr, real_right) == left
        || btor_aig_get_right_child (amgr, real_right) == left)
      return inc_aig_ref_counter_and_return (right);
  }
  /* symmetric rule of idempotency */
  if (btor_aig_is_and (real_right) && btor_aig_is_and (real_left)
      && !BTOR_IS_INVERTED_AIG (left) && !BTOR_IS_INVERTED_AIG (right))
  {
    if (btor_aig_get_left_child (amgr, real_left)
            == btor_aig_get_left_child (amgr, real_right)
        || btor_aig_get_right_child (amgr, real_left)
               == btor_aig_get_left_child (amgr, real_right))
    {
      right = btor_aig_get_right_child (amgr, real_right);
      goto BTOR_AIG_TWO_LEVEL_OPT_TRY_AGAIN;
    }
  }
  /* use commutativity */
  if (btor_aig_is_and (real_right) && btor_aig_is_and (real_left)
      && !BTOR_IS_INVERTED_AIG (left) && !BTOR_IS_INVERTED_AIG (right))
  {
    if (btor_aig_get_left_child (amgr, real_left)
            == btor_aig_get_right_child (amgr, real_right)
        || btor_aig_get_right_child (amgr, real_left)
               == btor_aig_get_right_child (amgr, real_right))
    {
      right = btor_aig_get_left_child (amgr, real_right);
      goto BTOR_AIG_TWO_LEVEL_OPT_TRY_AGAIN;
    }
  }
  /* asymmetric rule of substitution */
  if (btor_aig_is_and (real_left) && BTOR_IS_INVERTED_AIG (left))
  {
    if (btor_aig_get_right_child (amgr, real_left) == right)
    {
      left = BTOR_INVERT_AIG (btor_aig_get_left_child (amgr, real_left));
      goto BTOR_AIG_TWO_LEVEL_OPT_TRY_AGAIN;
    }
    if (btor_aig_get_left_child (amgr, real_left) == right)
    {
      left = BTOR_INVERT_AIG (btor_aig_get_right_child (amgr, real_left));
      goto BTOR_AIG_TWO_LEVEL_OPT_TRY_AGAIN;
    }
  }
  /* use commutativity */
  if (btor_aig_is_and (real_right) && BTOR_IS_INVERTED_AIG (right))
  {
    if (btor_aig_get_left_child (amgr, real_right) == left)
    {
      right = BTOR_INVERT_AIG (btor_aig_get_right_child (amgr, real_right));
      goto BTOR_AIG_TWO_LEVEL_OPT_TRY_AGAIN;
    }
    if (btor_aig_get_right_child (amgr, real_right) == left)
    {
      right = BTOR_INVERT_AIG (btor_aig_get_left_child (amgr, real_right));
      goto BTOR_AIG_TWO_LEVEL_OPT_TRY_AGAIN;
    }
  }
  /* symmetric rule of substitution */
  if (btor_aig_is_and (real_left) && BTOR_IS_INVERTED_AIG (left)
      && btor_aig_is_and (real_right) && !BTOR_IS_INVERTED_AIG (right))
  {
    if ((btor_aig_get_right_child (amgr, real_left)
         == btor_aig_get_left_child (amgr, real_right))
        || (btor_aig_get_right_child (amgr, real_left)
            == btor_aig_get_right_child (amgr, real_right)))
    {
      left = BTOR_INVERT_AIG (btor_aig_get_left_child (amgr, real_left));
      goto BTOR_AIG_TWO_LEVEL_OPT_TRY_AGAIN;
    }
    if ((btor_aig_get_left_child (amgr, real_left)
         == btor_aig_get_left_child (amgr, real_right))
        || (btor_aig_get_left_child (amgr, real_left)
            == btor_aig_get_right_child (amgr, real_right)))
    {
      left = BTOR_INVERT_AIG (btor_aig_get_right_child (amgr, real_left));
      goto BTOR_AIG_TWO_LEVEL_OPT_TRY_AGAIN;
    }
  }
  /* use commutativity */
  if (btor_aig_is_and (real_right) && BTOR_IS_INVERTED_AIG (right)
      && btor_aig_is_and (real_left) && !BTOR_IS_INVERTED_AIG (left))
  {
    if ((btor_aig_get_left_child (amgr, real_right)
         == btor_aig_get_right_child (amgr, real_left))
        || (btor_aig_get_left_child (amgr, real_right)
            == btor_aig_get_left_child (amgr, real_left)))
    {
      right = BTOR_INVERT_AIG (btor_aig_get_right_child (amgr, real_right));
      goto BTOR_AIG_TWO_LEVEL_OPT_TRY_AGAIN;
    }
    if ((btor_aig_get_right_child (amgr, real_right)
         == btor_aig_get_right_child (amgr, real_left))
        || (btor_aig_get_right_child (amgr, real_right)
            == btor_aig_get_left_child (amgr, real_left)))
    {
      right = BTOR_INVERT_AIG (btor_aig_get_left_child (amgr, real_right));
      goto BTOR_AIG_TWO_LEVEL_OPT_TRY_AGAIN;
    }
  }

  if (find_and_contradiction_aig (amgr, left, left, right, &calls)
      || find_and_contradiction_aig (amgr, right, left, right, &calls))
    return BTOR_AIG_FALSE;

  // Implicit XOR normalization .... (TODO keep it?)

  if (BTOR_IS_INVERTED_AIG (left) && btor_aig_is_and (real_left)
      && BTOR_IS_INVERTED_AIG (right) && btor_aig_is_and (real_right)
      && btor_aig_get_left_child (amgr, real_left)
             == BTOR_INVERT_AIG (btor_aig_get_left_child (amgr, real_right))
      && btor_aig_get_right_child (amgr, real_left)
             == BTOR_INVERT_AIG (btor_aig_get_right_child (amgr, real_right)))
  {
    BtorAIG *l = find_and_aig_node (
        amgr,
        btor_aig_get_left_child (amgr, real_left),
        BTOR_INVERT_AIG (btor_aig_get_right_child (amgr, real_left)));
    if (l)
    {
      BtorAIG *r = find_and_aig_node (
          amgr,
          BTOR_INVERT_AIG (btor_aig_get_left_child (amgr, real_left)),
          btor_aig_get_right_child (amgr, real_left));
      if (r)
      {
        res =
            find_and_aig_node (amgr, BTOR_INVERT_AIG (l), BTOR_INVERT_AIG (r));
        if (res)
        {
          inc_aig_ref_counter (res);
          return BTOR_INVERT_AIG (res);
        }
      }
    }
  }

  // TODO Implicit ITE normalization ....

  lookup = find_and_aig (amgr, left, right);
  assert (lookup);
  res = *lookup ? btor_aig_get_by_id (amgr, *lookup) : 0;
  if (!res)
  {
    if (amgr->table.num_elements == amgr->table.size
        && btor_util_log_2 (amgr->table.size) < BTOR_AIG_UNIQUE_TABLE_LIMIT)
    {
      enlarge_aig_nodes_unique_table (amgr);
      lookup = find_and_aig (amgr, left, right);
    }
    if (btor_opt_get (amgr->btor, BTOR_OPT_SORT_AIG) > 0
        && real_right->id < real_left->id)
    {
      BTOR_SWAP (BtorAIG *, left, right);
    }
    res     = new_and_aig (amgr, left, right);
    *lookup = res->id;
    inc_aig_ref_counter (left);
    inc_aig_ref_counter (right);
    assert (amgr->table.num_elements < INT32_MAX);
    amgr->table.num_elements++;
  }
  else
  {
    inc_aig_ref_counter (res);
  }
  return res;
}

BtorAIG *
btor_aig_or (BtorAIGMgr *amgr, BtorAIG *left, BtorAIG *right)
{
  assert (amgr);
  return BTOR_INVERT_AIG (
      btor_aig_and (amgr, BTOR_INVERT_AIG (left), BTOR_INVERT_AIG (right)));
}

BtorAIG *
btor_aig_eq (BtorAIGMgr *amgr, BtorAIG *left, BtorAIG *right)
{
  BtorAIG *eq, *eq_left, *eq_right;
  assert (amgr);

  eq_left =
      BTOR_INVERT_AIG (btor_aig_and (amgr, left, BTOR_INVERT_AIG (right)));
  eq_right =
      BTOR_INVERT_AIG (btor_aig_and (amgr, BTOR_INVERT_AIG (left), right));
  eq = btor_aig_and (amgr, eq_left, eq_right);
  btor_aig_release (amgr, eq_left);
  btor_aig_release (amgr, eq_right);
  return eq;
}

BtorAIG *
btor_aig_cond (BtorAIGMgr *amgr,
               BtorAIG *a_cond,
               BtorAIG *a_if,
               BtorAIG *a_else)
{
  BtorAIG *cond, *and1, *and2;
  assert (amgr);
  and1 = btor_aig_and (amgr, a_if, a_cond);
  and2 = btor_aig_and (amgr, a_else, BTOR_INVERT_AIG (a_cond));
  cond = btor_aig_or (amgr, and1, and2);
  btor_aig_release (amgr, and1);
  btor_aig_release (amgr, and2);
  return cond;
}

BtorAIGMgr *
btor_aig_mgr_new (Btor *btor)
{
  assert (btor);

  BtorAIGMgr *amgr;

  BTOR_CNEW (btor->mm, amgr);
  amgr->btor = btor;
  BTOR_INIT_AIG_UNIQUE_TABLE (btor->mm, amgr->table);
  amgr->smgr = btor_sat_mgr_new (btor);
  BTOR_INIT_STACK (btor->mm, amgr->id2aig);
  BTOR_PUSH_STACK (amgr->id2aig, BTOR_AIG_FALSE);
  BTOR_PUSH_STACK (amgr->id2aig, BTOR_AIG_TRUE);
  assert ((size_t) BTOR_AIG_FALSE == 0);
  assert ((size_t) BTOR_AIG_TRUE == 1);
  BTOR_INIT_STACK (btor->mm, amgr->cnfid2aig);
  return amgr;
}

static BtorAIG *
clone_aig (BtorMemMgr *mm, BtorAIG *aig)
{
  assert (mm);

  size_t size;
  BtorAIG *res, *real_aig;

  if (btor_aig_is_const (aig)) return aig;

  real_aig = BTOR_REAL_ADDR_AIG (aig);
  size     = sizeof (BtorAIG);
  if (!real_aig->is_var) size += 2 * sizeof (int32_t);
  res = btor_mem_malloc (mm, size);
  memcpy (res, real_aig, size);

  res = BTOR_IS_INVERTED_AIG (aig) ? BTOR_INVERT_AIG (res) : res;
  return res;
}

static void
clone_aigs (BtorAIGMgr *amgr, BtorAIGMgr *clone)
{
  assert (amgr);
  assert (clone);

  uint32_t i;
  size_t size;
  BtorMemMgr *mm;
  BtorAIG *aig;

  mm = clone->btor->mm;

  /* clone id2aig table */
  BTOR_INIT_STACK (mm, clone->id2aig);
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
  BTOR_INIT_STACK (mm, clone->cnfid2aig);
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
btor_aig_mgr_clone (Btor *btor, BtorAIGMgr *amgr)
{
  assert (btor);
  assert (amgr);

  BtorAIGMgr *res;

  BTOR_CNEW (btor->mm, res);
  res->btor = btor;

  res->smgr = btor_sat_mgr_clone (btor, amgr->smgr);
  /* Note: we do not yet clone aigs here (we need the clone of the aig
   *       manager for that). */
  res->max_num_aigs     = amgr->max_num_aigs;
  res->max_num_aig_vars = amgr->max_num_aig_vars;
  res->cur_num_aigs     = amgr->cur_num_aigs;
  res->cur_num_aig_vars = amgr->cur_num_aig_vars;
  res->num_cnf_vars     = amgr->num_cnf_vars;
  res->num_cnf_clauses  = amgr->num_cnf_clauses;
  res->num_cnf_literals = amgr->num_cnf_literals;
  clone_aigs (amgr, res);
  return res;
}

void
btor_aig_mgr_delete (BtorAIGMgr *amgr)
{
  BtorMemMgr *mm;
  assert (amgr);
  assert (getenv ("BTORLEAK") || getenv ("BTORLEAKAIG")
          || amgr->table.num_elements == 0);
  mm = amgr->btor->mm;
  BTOR_RELEASE_AIG_UNIQUE_TABLE (mm, amgr->table);
  btor_sat_mgr_delete (amgr->smgr);
  BTOR_RELEASE_STACK (amgr->id2aig);
  BTOR_RELEASE_STACK (amgr->cnfid2aig);
  BTOR_DELETE (mm, amgr);
}

static bool
is_xor_aig (BtorAIGMgr *amgr, BtorAIG *aig, BtorAIGPtrStack *leafs)
{
#ifdef BTOR_AIG_TO_CNF_EXTRACT_XOR
  BtorAIG *l, *r, *ll, *lr, *rl, *rr;

  assert (btor_aig_is_and (aig));
  assert (!BTOR_IS_INVERTED_AIG (aig));

  l = btor_aig_get_left_child (amgr, aig);
  if (!BTOR_IS_INVERTED_AIG (l)) return false;
  l = BTOR_REAL_ADDR_AIG (l);
#ifdef BTOR_AIG_TO_CNF_EXTRACT_ONLY_NON_SHARED
  if (l->refs > 1) return false;
#endif

  r = btor_aig_get_right_child (amgr, aig);
  if (!BTOR_IS_INVERTED_AIG (r)) return false;
  r = BTOR_REAL_ADDR_AIG (r);
#ifdef BTOR_AIG_TO_CNF_EXTRACT_ONLY_NON_SHARED
  if (r->refs > 1) return false;
#endif

  ll = btor_aig_get_left_child (amgr, l);
  lr = btor_aig_get_right_child (amgr, l);

  rl = btor_aig_get_left_child (amgr, r);
  rr = btor_aig_get_right_child (amgr, r);

  if (ll == BTOR_INVERT_AIG (rl) && lr == BTOR_INVERT_AIG (rr))
  {
    BTOR_PUSH_STACK (*leafs, rr);
    BTOR_PUSH_STACK (*leafs, ll);
    return true;
  }

  assert (!btor_opt_get (amgr->btor, BTOR_OPT_SORT_AIG)
          || ll != BTOR_INVERT_AIG (rr) || lr != BTOR_INVERT_AIG (rl));

  return false;
#else
  (void) amgr;
  (void) aig;
  (void) leafs;
  return false;
#endif
}

static bool
is_ite_aig (BtorAIGMgr *amgr, BtorAIG *aig, BtorAIGPtrStack *leafs)
{
#ifdef BTOR_AIG_TO_CNF_EXTRACT_ITE
  BtorAIG *l, *r, *ll, *lr, *rl, *rr;

  assert (btor_aig_is_and (aig));
  assert (!BTOR_IS_INVERTED_AIG (aig));

  l = btor_aig_get_left_child (amgr, aig);
  if (!BTOR_IS_INVERTED_AIG (l)) return false;
  l = BTOR_REAL_ADDR_AIG (l);
#ifdef BTOR_AIG_TO_CNF_EXTRACT_ONLY_NON_SHARED
  if (l->refs > 1) return false;
#endif

  r = btor_aig_get_right_child (amgr, aig);
  if (!BTOR_IS_INVERTED_AIG (r)) return false;
  r = BTOR_REAL_ADDR_AIG (r);
#ifdef BTOR_AIG_TO_CNF_EXTRACT_ONLY_NON_SHARED
  if (r->refs > 1) return false;
#endif

  ll = btor_aig_get_left_child (amgr, l);
  lr = btor_aig_get_right_child (amgr, l);

  rl = btor_aig_get_left_child (amgr, r);
  rr = btor_aig_get_right_child (amgr, r);

  // aig == (!ll | !lr)(!rl | !rr)

  if (BTOR_INVERT_AIG (lr) == rl)
  {
    // aig == (!rl -> !ll)(rl -> !rr) = rl ? !rr : !ll
    BTOR_PUSH_STACK (*leafs, BTOR_INVERT_AIG (ll));  // else
    BTOR_PUSH_STACK (*leafs, BTOR_INVERT_AIG (rr));  // then
    BTOR_PUSH_STACK (*leafs, rl);                    // cond
    return true;
  }
  if (BTOR_INVERT_AIG (ll) == rl)
  {
    // aig == (!rl -> !lr)(rl -> !rr)
    BTOR_PUSH_STACK (*leafs, BTOR_INVERT_AIG (lr));  // else
    BTOR_PUSH_STACK (*leafs, BTOR_INVERT_AIG (rr));  // then
    BTOR_PUSH_STACK (*leafs, rl);                    // cond
    return true;
  }
  if (BTOR_INVERT_AIG (lr) == rr)
  {
    // aig == (!rr -> !ll)(rr -> !rl)
    BTOR_PUSH_STACK (*leafs, BTOR_INVERT_AIG (ll));  // else
    BTOR_PUSH_STACK (*leafs, BTOR_INVERT_AIG (rl));  // then
    BTOR_PUSH_STACK (*leafs, rr);                    // cond
    return true;
  }
  if (BTOR_INVERT_AIG (ll) == rr)
  {
    // aig == (!rr -> !lr)(rr -> !rl)
    BTOR_PUSH_STACK (*leafs, BTOR_INVERT_AIG (lr));  // else
    BTOR_PUSH_STACK (*leafs, BTOR_INVERT_AIG (rl));  // then
    BTOR_PUSH_STACK (*leafs, rr);                    // cond
    return true;
  }

  return false;
#else
  (void) amgr;
  (void) aig;
  (void) leafs;
  return false;
#endif
}

static void
set_next_id_aig_mgr (BtorAIGMgr *amgr, BtorAIG *root)
{
  assert (!BTOR_IS_INVERTED_AIG (root));
  assert (!root->cnf_id);
  root->cnf_id = btor_sat_mgr_next_cnf_id (amgr->smgr);
  assert (root->cnf_id > 0);
  BTOR_FIT_STACK (amgr->cnfid2aig, (size_t) root->cnf_id);
  amgr->cnfid2aig.start[root->cnf_id] = root->id;
  assert (amgr->cnfid2aig.start[root->cnf_id] == root->id);
  amgr->num_cnf_vars++;
}

#ifdef BTOR_EXTRACT_TOP_LEVEL_MULTI_OR
static bool
is_or_aig (BtorAIGMgr *amgr, BtorAIG *root, BtorAIGPtrStack *leafs)
{
  assert (amgr);
  assert (root);
  assert (leafs);
  assert (BTOR_EMPTY_STACK (*leafs));

  BtorAIG *real_cur, *cur, **p;
  BtorAIGPtrStack tree;
  BtorMemMgr *mm;

  if (!BTOR_IS_INVERTED_AIG (root)
      || !btor_aig_is_and (BTOR_REAL_ADDR_AIG (root)))
    return false;

  mm   = amgr->btor->mm;
  root = BTOR_REAL_ADDR_AIG (root);

  BTOR_INIT_STACK (mm, tree);
  BTOR_PUSH_STACK (tree, btor_aig_get_right_child (amgr, root));
  BTOR_PUSH_STACK (tree, btor_aig_get_left_child (amgr, root));

  while (!BTOR_EMPTY_STACK (tree))
  {
    cur      = BTOR_POP_STACK (tree);
    real_cur = BTOR_REAL_ADDR_AIG (cur);

    if (btor_aig_is_const (real_cur))
    {
      assert (cur == BTOR_AIG_FALSE);
      continue;
    }

    if (real_cur->mark) continue;

    if (!BTOR_IS_INVERTED_AIG (cur) && btor_aig_is_and (real_cur))
    {
      BTOR_PUSH_STACK (tree, btor_aig_get_right_child (amgr, real_cur));
      BTOR_PUSH_STACK (tree, btor_aig_get_left_child (amgr, real_cur));
    }
    else
    {
      BTOR_PUSH_STACK (*leafs, cur);
      real_cur->mark = 1;
    }
  }

  for (p = (*leafs).start; p < (*leafs).top; p++)
  {
    cur = *p;
    assert (BTOR_REAL_ADDR_AIG (cur)->mark);
    BTOR_REAL_ADDR_AIG (cur)->mark = 0;
  }

  BTOR_RELEASE_STACK (tree);
  return true;
}
#endif

void
btor_aig_to_sat_tseitin (BtorAIGMgr *amgr, BtorAIG *start)
{
  BtorAIGPtrStack stack, tree, leafs, marked;
  int32_t x, y, a, b, c;
  bool isxor, isite;
  BtorAIG *root, *cur;
  BtorSATMgr *smgr;
  BtorMemMgr *mm;
  uint32_t local;
  BtorAIG **p;

  if (btor_aig_is_const (start)) return;

  assert (amgr);

  smgr = amgr->smgr;
  mm   = amgr->btor->mm;

  BTOR_INIT_STACK (mm, stack);
  BTOR_INIT_STACK (mm, tree);
  BTOR_INIT_STACK (mm, leafs);
  BTOR_INIT_STACK (mm, marked);

  start = BTOR_REAL_ADDR_AIG (start);
  BTOR_PUSH_STACK (stack, start);

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

    if (btor_aig_is_var (root))
    {
      set_next_id_aig_mgr (amgr, root);
      continue;
    }

    assert (root->mark < 2);
    assert (btor_aig_is_and (root));
    assert (BTOR_EMPTY_STACK (tree));
    assert (BTOR_EMPTY_STACK (leafs));

    if ((isxor = is_xor_aig (amgr, root, &leafs)))
      isite = 0;
    else
      isite = is_ite_aig (amgr, root, &leafs);

    if (!isxor && !isite)
    {
#ifdef BTOR_AIG_TO_CNF_NARY_AND
      BTOR_PUSH_STACK (tree, btor_aig_get_right_child (amgr, root));
      BTOR_PUSH_STACK (tree, btor_aig_get_left_child (amgr, root));

      while (!BTOR_EMPTY_STACK (tree))
      {
        cur = BTOR_POP_STACK (tree);

        if (BTOR_IS_INVERTED_AIG (cur) || btor_aig_is_var (cur)
            || cur->refs > 1u || cur->cnf_id)
        {
          BTOR_PUSH_STACK (leafs, cur);
        }
        else
        {
          BTOR_PUSH_STACK (tree, btor_aig_get_right_child (amgr, cur));
          BTOR_PUSH_STACK (tree, btor_aig_get_left_child (amgr, cur));
        }
      }
#else
      BTOR_PUSH_STACK (leafs, btor_aig_get_left_child (amgr, root));
      BTOR_PUSH_STACK (leafs, btor_aig_get_right_child (amgr, root));
#endif
    }

    if (root->mark == 0)
    {
      root->mark = 1;
      assert (root->refs >= 1);
      assert (!root->local);
      root->local = 1;
      BTOR_PUSH_STACK (marked, root);
      BTOR_PUSH_STACK (stack, root);
      for (p = leafs.start; p < leafs.top; p++) BTOR_PUSH_STACK (stack, *p);
    }
    else
    {
      assert (root->mark == 1);
      root->mark = 2;

      set_next_id_aig_mgr (amgr, root);
      x = root->cnf_id;
      assert (x);

      if (isxor)
      {
        assert (BTOR_COUNT_STACK (leafs) == 2);
        a = btor_aig_get_cnf_id (leafs.start[0]);
        b = btor_aig_get_cnf_id (leafs.start[1]);

        btor_sat_add (smgr, -x);
        btor_sat_add (smgr, a);
        btor_sat_add (smgr, -b);
        btor_sat_add (smgr, 0);

        btor_sat_add (smgr, -x);
        btor_sat_add (smgr, -a);
        btor_sat_add (smgr, b);
        btor_sat_add (smgr, 0);

        btor_sat_add (smgr, x);
        btor_sat_add (smgr, -a);
        btor_sat_add (smgr, -b);
        btor_sat_add (smgr, 0);

        btor_sat_add (smgr, x);
        btor_sat_add (smgr, a);
        btor_sat_add (smgr, b);
        btor_sat_add (smgr, 0);
        amgr->num_cnf_clauses += 4;
        amgr->num_cnf_literals += 12;
      }
      else if (isite)
      {
        assert (BTOR_COUNT_STACK (leafs) == 3);
        a = btor_aig_get_cnf_id (leafs.start[0]);  // else
        b = btor_aig_get_cnf_id (leafs.start[1]);  // then
        c = btor_aig_get_cnf_id (leafs.start[2]);  // cond

        btor_sat_add (smgr, -x);
        btor_sat_add (smgr, -c);
        btor_sat_add (smgr, b);
        btor_sat_add (smgr, 0);

        btor_sat_add (smgr, -x);
        btor_sat_add (smgr, c);
        btor_sat_add (smgr, a);
        btor_sat_add (smgr, 0);

        btor_sat_add (smgr, x);
        btor_sat_add (smgr, -c);
        btor_sat_add (smgr, -b);
        btor_sat_add (smgr, 0);

        btor_sat_add (smgr, x);
        btor_sat_add (smgr, c);
        btor_sat_add (smgr, -a);
        btor_sat_add (smgr, 0);
        amgr->num_cnf_clauses += 4;
        amgr->num_cnf_literals += 12;
      }
      else
      {
        for (p = leafs.start; p < leafs.top; p++)
        {
          cur = *p;
          y   = btor_aig_get_cnf_id (cur);
          assert (y);
          btor_sat_add (smgr, -y);
          amgr->num_cnf_literals++;
        }
        btor_sat_add (smgr, x);
        btor_sat_add (smgr, 0);
        amgr->num_cnf_clauses++;
        amgr->num_cnf_literals++;

        for (p = leafs.start; p < leafs.top; p++)
        {
          cur = *p;
          y   = btor_aig_get_cnf_id (cur);
          btor_sat_add (smgr, -x);
          btor_sat_add (smgr, y);
          btor_sat_add (smgr, 0);
          amgr->num_cnf_clauses++;
          amgr->num_cnf_literals += 2;
        }
      }
    }
    BTOR_RESET_STACK (leafs);
  }
  BTOR_RELEASE_STACK (stack);
  BTOR_RELEASE_STACK (leafs);
  BTOR_RELEASE_STACK (tree);

  while (!BTOR_EMPTY_STACK (marked))
  {
    cur = BTOR_POP_STACK (marked);
    assert (!BTOR_IS_INVERTED_AIG (cur));
    assert (cur->mark > 0);
    cur->mark = 0;
    assert (cur->cnf_id);
    assert (btor_aig_is_and (cur));
    local = cur->local;
    assert (local > 0);
    cur->local = 0;
    if (cur == start) continue;
    assert (cur->refs >= local);
    if (cur->refs > local) continue;
    release_cnf_id_aig_mgr (amgr, cur);
  }
  BTOR_RELEASE_STACK (marked);
}

static void
aig_to_sat_tseitin (BtorAIGMgr *amgr, BtorAIG *aig)
{
  assert (amgr);
  assert (!btor_aig_is_const (aig));
  BTOR_MSG (amgr->btor->msg,
            3,
            "transforming AIG into CNF using Tseitin transformation");
  btor_aig_to_sat_tseitin (amgr, aig);
}

void
btor_aig_to_sat (BtorAIGMgr *amgr, BtorAIG *aig)
{
  assert (amgr);
  if (!btor_sat_is_initialized (amgr->smgr)) return;
  if (!btor_aig_is_const (aig)) aig_to_sat_tseitin (amgr, aig);
}

void
btor_aig_add_toplevel_to_sat (BtorAIGMgr *amgr, BtorAIG *root)
{
  assert (amgr);
  assert (root);

  if (!btor_sat_is_initialized (amgr->smgr)) return;

#ifdef BTOR_AIG_TO_CNF_TOP_ELIM
  BtorMemMgr *mm;
  BtorSATMgr *smgr;
  BtorAIG *aig, *left;
  BtorAIGPtrStack stack;
#ifdef BTOR_EXTRACT_TOP_LEVEL_MULTI_OR
  BtorAIGPtrStack leafs;
  BtorAIG **p;
#else
  BtorAIG *real_aig, *right;
#endif

  mm   = amgr->btor->mm;
  smgr = amgr->smgr;

  if (!btor_sat_is_initialized (smgr)) return;

  if (root == BTOR_AIG_TRUE) return;

  if (root == BTOR_AIG_FALSE)
  {
    btor_sat_add (smgr, 0); /* add empty clause */
    amgr->num_cnf_clauses++;
    return;
  }

  BTOR_INIT_STACK (mm, stack);
  aig = root;
  goto BTOR_ADD_TOPLEVEL_AIG_TO_SAT_WITHOUT_POP;

  while (!BTOR_EMPTY_STACK (stack))
  {
    aig = BTOR_POP_STACK (stack);
  BTOR_ADD_TOPLEVEL_AIG_TO_SAT_WITHOUT_POP:
    if (!BTOR_IS_INVERTED_AIG (aig) && btor_aig_is_and (aig))
    {
      BTOR_PUSH_STACK (stack, btor_aig_get_right_child (amgr, aig));
      BTOR_PUSH_STACK (stack, btor_aig_get_left_child (amgr, aig));
    }
    else
    {
#ifdef BTOR_EXTRACT_TOP_LEVEL_MULTI_OR
      BTOR_INIT_STACK (mm, leafs);
      if (is_or_aig (amgr, aig, &leafs))
      {
        assert (BTOR_COUNT_STACK (leafs) > 1);
        for (p = leafs.start; p < leafs.top; p++)
        {
          left = *p;
          if (btor_aig_is_const (left))  // TODO reachable?
            continue;
          btor_aig_to_sat (amgr, left);
        }
        for (p = leafs.start; p < leafs.top; p++)
        {
          left = *p;
          assert (btor_aig_get_cnf_id (left));
          btor_sat_add (smgr, btor_aig_get_cnf_id (BTOR_INVERT_AIG (left)));
          amgr->num_cnf_literals++;
        }
        btor_sat_add (smgr, 0);
        amgr->num_cnf_clauses++;
      }
      else
      {
        btor_aig_to_sat (amgr, aig);
        btor_sat_add (smgr, btor_aig_get_cnf_id (aig));
        btor_sat_add (smgr, 0);
        amgr->num_cnf_literals++;
        amgr->num_cnf_clauses++;
      }
      BTOR_RELEASE_STACK (leafs);
#else
      real_aig = BTOR_REAL_ADDR_AIG (aig);
      if (BTOR_IS_INVERTED_AIG (aig) && btor_aig_is_and (real_aig))
      {
        left  = BTOR_INVERT_AIG (btor_aig_get_left_child (amgr, real_aig));
        right = BTOR_INVERT_AIG (btor_aig_get_right_child (amgr, real_aig));
        btor_aig_to_sat (amgr, left);
        btor_aig_to_sat (amgr, right);
        btor_sat_add (smgr, btor_aig_get_cnf_id (left));
        btor_sat_add (smgr, btor_aig_get_cnf_id (right));
        btor_sat_add (smgr, 0);
        amgr->num_cnf_clauses++;
        amgr->num_cnf_literals += 2;
      }
      else
      {
        btor_aig_to_sat (amgr, aig);
        btor_sat_add (smgr, btor_aig_get_cnf_id (aig));
        btor_sat_add (smgr, 0);
        amgr->num_cnf_clauses++;
        amgr->num_cnf_literals++;
      }
#endif
    }
  }
  BTOR_RELEASE_STACK (stack);
#else
  if (root == BTOR_AIG_TRUE) return;

  if (root == BTOR_AIG_FALSE)
  {
    btor_sat_add (amgr->smgr, 0);
    return;
  }
  btor_aig_to_sat (amgr, root);
  btor_sat_add (amgr->smgr, btor_aig_get_cnf_id (root));
  btor_sat_add (amgr->smgr, 0);
#endif
}

BtorSATMgr *
btor_aig_get_sat_mgr (const BtorAIGMgr *amgr)
{
  return amgr ? amgr->smgr : 0;
}

int32_t
btor_aig_get_assignment (BtorAIGMgr *amgr, BtorAIG *aig)
{
  assert (amgr);
  if (aig == BTOR_AIG_TRUE) return 1;
  if (aig == BTOR_AIG_FALSE) return -1;

  /* Note: If an AIG is not yet encoded to SAT or if the SAT solver returns
   * undefined for a variable, we implicitly initialize it with false (-1). */
  int32_t val = -1;
  if (BTOR_REAL_ADDR_AIG (aig)->cnf_id > 0)
  {
    val = btor_sat_deref (amgr->smgr, BTOR_REAL_ADDR_AIG (aig)->cnf_id);
    if (val == 0)
    {
      val = -1;
    }
  }
  return BTOR_IS_INVERTED_AIG (aig) ? -val : val;
}

int32_t
btor_aig_compare (const BtorAIG *aig0, const BtorAIG *aig1)
{
  if (aig0 == aig1) return 0;
  if (BTOR_INVERT_AIG (aig0) == aig1)
    return BTOR_IS_INVERTED_AIG (aig0) ? -1 : 1;
  if (BTOR_IS_INVERTED_AIG (aig0)) aig0 = BTOR_INVERT_AIG (aig0);
  if (aig0 == BTOR_AIG_FALSE) return -1;
  assert (aig0 != BTOR_AIG_TRUE);
  if (BTOR_IS_INVERTED_AIG (aig1)) aig1 = BTOR_INVERT_AIG (aig1);
  if (aig1 == BTOR_AIG_FALSE) return 1;
  assert (aig1 != BTOR_AIG_TRUE);
  return aig0->id - aig1->id;
}

/* hash AIG by id */
uint32_t
btor_aig_hash_by_id (const BtorAIG *aig)
{
  assert (aig);
  return (uint32_t) btor_aig_get_id (aig) * 7334147u;
}

/* compare AIG by id */
int32_t
btor_aig_compare_by_id (const BtorAIG *aig0, const BtorAIG *aig1)
{
  assert (aig0);
  assert (aig1);

  int32_t id0, id1;

  id0 = btor_aig_get_id (aig0);
  id1 = btor_aig_get_id (aig1);
  if (id0 < id1) return -1;
  if (id0 > id1) return 1;
  return 0;
}

int32_t
btor_compare_aig_by_id_qsort_asc (const void *aig0, const void *aig1)
{
  assert (aig0);
  assert (!btor_aig_is_const (aig0));
  assert (aig1);
  assert (!btor_aig_is_const (aig1));

  int32_t id0, id1;

  id0 = BTOR_REAL_ADDR_AIG (*(BtorAIG **) aig0)->id;
  id1 = BTOR_REAL_ADDR_AIG (*(BtorAIG **) aig1)->id;
  return id0 - id1;
}
