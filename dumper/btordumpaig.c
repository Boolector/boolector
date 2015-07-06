/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2014 Armin Biere.
 *  Copyright (C) 2015 Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "dumper/btordumpaig.h"
#include "btoraigvec.h"
#include "btorexit.h"
#include "utils/btoriter.h"

#define BTOR_ABORT_DUMPAIG(cond, msg)                   \
  do                                                    \
  {                                                     \
    if (cond)                                           \
    {                                                   \
      printf ("[btordumpaig] %s: %s\n", __func__, msg); \
      fflush (stdout);                                  \
      exit (BTOR_ERR_EXIT);                             \
    }                                                   \
  } while (0)

static unsigned
aiger_encode_aig (BtorPtrHashTable *table, BtorAIG *aig)
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
btor_dump_aig (BtorAIGMgr *amgr, int binary, FILE *output, BtorAIG *aig)
{
  btor_dump_seq_aiger (amgr, binary, output, 1, &aig, 0, 0, 0, 0);
}

void
btor_dump_aiger (Btor *btor, FILE *output, bool is_binary)
{
  BtorHashTableIterator it;
  BtorPtrHashTable *backannotation;
  BtorAIGVec *av;
  BtorAIG *tmp, *merged;
  BtorAIGMgr *amgr;
  BtorAIGVecMgr *avmgr;
  int lazy_synthesize;

  amgr           = btor_get_aig_mgr_btor (btor);
  avmgr          = btor->avmgr;
  backannotation = btor_new_ptr_hash_table (btor->mm, 0, 0);

  (void) btor_simplify (btor);

  BTOR_ABORT_DUMPAIG (
      btor->ops[BTOR_UF_NODE].cur > 0 || btor->ops[BTOR_LAMBDA_NODE].cur > 0,
      "cannot dump to AIGER format if formula contains "
      "functions");

  /* do not encode AIGs to SAT */
  lazy_synthesize                   = btor->options.lazy_synthesize.val;
  btor->options.lazy_synthesize.val = 1;
  btor_init_node_hash_table_iterator (&it, btor->unsynthesized_constraints);
  btor_queue_node_hash_table_iterator (&it, btor->synthesized_constraints);
  merged = BTOR_AIG_TRUE;
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    av = btor_exp_to_aigvec (
        btor, btor_next_node_hash_table_iterator (&it), backannotation);
    assert (av->len == 1);
    tmp = btor_and_aig (amgr, merged, av->aigs[0]);
    btor_release_aig (amgr, merged);
    merged = tmp;
    btor_release_delete_aigvec (avmgr, av);
  }
  btor->options.lazy_synthesize.val = lazy_synthesize;

  btor_dump_seq_aiger (
      amgr, is_binary, output, 1, &merged, 0, 0, 0, backannotation);

  btor_release_aig (amgr, merged);

  btor_init_hash_table_iterator (&it, backannotation);
  while (btor_has_next_hash_table_iterator (&it))
  {
    btor_freestr (btor->mm, it.bucket->data.asStr);
    (void) btor_next_hash_table_iterator (&it);
  }
  btor_delete_ptr_hash_table (backannotation);
}

void
btor_dump_seq_aiger (BtorAIGMgr *amgr,
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
    if (!binary) fprintf (file, "%u ", aiger_encode_aig (table, regs[i]));

    fprintf (file, "%u\n", aiger_encode_aig (table, nexts[i]));
  }

  /* Then the outputs ...
   */
  for (i = 0; i < naigs; i++)
    fprintf (file, "%u\n", aiger_encode_aig (table, aigs[i]));

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
    left_id  = aiger_encode_aig (table, left);
    right_id = aiger_encode_aig (table, right);

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
      //	  assert (p->data.asInt == i + l + 1);
      if (btor_find_in_ptr_hash_table (latches, aig))
        fprintf (file, "l%d %s\n", l++, b->data.asStr);
      else
        fprintf (file, "i%d %s\n", i++, b->data.asStr);
    }
  }

  btor_delete_ptr_hash_table (table);
  btor_delete_ptr_hash_table (latches);
}
