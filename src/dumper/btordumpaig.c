/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2015 Armin Biere.
 *  Copyright (C) 2015-2016 Mathias Preiner.
 *  Copyright (C) 2016-2017 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btordumpaig.h"

#include "btorabort.h"
#include "btoraigvec.h"
#include "utils/btornodeiter.h"
#include "utils/btorutil.h"

static unsigned
aiger_encode_aig (BtorPtrHashTable *table, BtorAIG *aig)
{
  BtorPtrHashBucket *b;
  BtorAIG *real_aig;
  unsigned res;

  if (aig == BTOR_AIG_FALSE) return 0;

  if (aig == BTOR_AIG_TRUE) return 1;

  real_aig = BTOR_REAL_ADDR_AIG (aig);

  b = btor_hashptr_table_get (table, real_aig);
  assert (b);

  res = 2 * (unsigned) b->data.as_int;

  if (BTOR_IS_INVERTED_AIG (aig)) res ^= 1;

  return res;
}

void
btor_dumpaig_dump_aig (BtorAIGMgr *amgr, int binary, FILE *output, BtorAIG *aig)
{
  btor_dumpaig_dump_seq (amgr, binary, output, 1, &aig, 0, 0, 0, 0);
}

void
btor_dumpaig_dump (Btor *btor, FILE *output, bool is_binary, bool merge_roots)
{
  assert (btor->lambdas->count == 0);
  assert (btor->ufs->count == 0);

  BtorPtrHashTableIterator it;
  BtorPtrHashTable *backannotation;
  BtorAIGVec *av;
  BtorAIG *tmp, *merged;
  BtorAIGMgr *amgr;
  BtorAIGVecMgr *avmgr;
  int lazy_synthesize;
  BtorAIGPtrStack roots;

  BTOR_INIT_STACK (btor->mm, roots);
  amgr           = btor_get_aig_mgr (btor);
  avmgr          = btor->avmgr;
  backannotation = btor_hashptr_table_new (btor->mm, 0, 0);

  BTOR_ABORT (
      btor->ops[BTOR_UF_NODE].cur > 0 || btor->ops[BTOR_LAMBDA_NODE].cur > 0,
      "cannot dump to AIGER format if formula contains "
      "functions");

  /* do not encode AIGs to SAT */
  lazy_synthesize = btor_opt_get (btor, BTOR_OPT_FUN_LAZY_SYNTHESIZE);
  btor_opt_set (btor, BTOR_OPT_FUN_LAZY_SYNTHESIZE, 1);
  btor_iter_hashptr_init (&it, btor->unsynthesized_constraints);
  btor_iter_hashptr_queue (&it, btor->synthesized_constraints);
  merged = BTOR_AIG_TRUE;
  while (btor_iter_hashptr_has_next (&it))
  {
    av =
        btor_exp_to_aigvec (btor, btor_iter_hashptr_next (&it), backannotation);
    assert (av->len == 1);
    if (merge_roots)
    {
      tmp = btor_aig_and (amgr, merged, av->aigs[0]);
      btor_aig_release (amgr, merged);
      merged = tmp;
    }
    else
      BTOR_PUSH_STACK (roots, btor_aig_copy (amgr, av->aigs[0]));
    btor_aigvec_release_delete (avmgr, av);
  }
  btor_opt_set (btor, BTOR_OPT_FUN_LAZY_SYNTHESIZE, lazy_synthesize);
  if (merge_roots) BTOR_PUSH_STACK (roots, merged);

  if (BTOR_EMPTY_STACK (roots))
    BTOR_PUSH_STACK (roots,
                     btor->inconsistent ? BTOR_AIG_FALSE : BTOR_AIG_TRUE);

  btor_dumpaig_dump_seq (amgr,
                         is_binary,
                         output,
                         BTOR_COUNT_STACK (roots),
                         roots.start,
                         0,
                         0,
                         0,
                         backannotation);

  while (!BTOR_EMPTY_STACK (roots))
    btor_aig_release (amgr, BTOR_POP_STACK (roots));
  BTOR_RELEASE_STACK (roots);

  btor_iter_hashptr_init (&it, backannotation);
  while (btor_iter_hashptr_has_next (&it))
  {
    btor_mem_freestr (btor->mm, it.bucket->data.as_str);
    (void) btor_iter_hashptr_next (&it);
  }
  btor_hashptr_table_delete (backannotation);
}

void
btor_dumpaig_dump_seq (BtorAIGMgr *amgr,
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

  assert (naigs >= 0);

  mm = amgr->btor->mm;

  table   = btor_hashptr_table_new (mm, 0, 0);
  latches = btor_hashptr_table_new (mm, 0, 0);

  /* First add latches and inputs to hash tables.
   */
  for (i = nregs - 1; i >= 0; i--)
  {
    aig = regs[i];
    assert (!btor_aig_is_const (aig));
    assert (!btor_hashptr_table_get (latches, aig));
    btor_hashptr_table_add (latches, aig);
  }

  BTOR_INIT_STACK (mm, stack);
  for (i = naigs - 1; i >= 0; i--)
  {
    aig = aigs[i];
    if (!btor_aig_is_const (aig)) BTOR_PUSH_STACK (stack, aig);
  }
  for (i = nregs - 1; i >= 0; i--)
  {
    aig = nexts[i];
    if (!btor_aig_is_const (aig)) BTOR_PUSH_STACK (stack, aig);
  }

  M = 0;

  while (!BTOR_EMPTY_STACK (stack))
  {
    aig = BTOR_POP_STACK (stack);

  CONTINUE_WITHOUT_POP:

    assert (!btor_aig_is_const (aig));
    aig = BTOR_REAL_ADDR_AIG (aig);

    if (aig->mark) continue;

    aig->mark = 1;

    if (btor_aig_is_var (aig))
    {
      if (btor_hashptr_table_get (latches, aig)) continue;

      p              = btor_hashptr_table_add (table, aig);
      p->data.as_int = ++M;
      assert (M > 0);
    }
    else
    {
      assert (btor_aig_is_and (aig));

      right = btor_aig_get_right_child (amgr, aig);
      BTOR_PUSH_STACK (stack, right);

      aig = btor_aig_get_left_child (amgr, aig);
      goto CONTINUE_WITHOUT_POP;
    }
  }

  for (i = 0; i < nregs; i++)
  {
    aig = regs[i];
    assert (!btor_aig_is_const (aig));
    assert (btor_hashptr_table_get (latches, aig));
    assert (!btor_hashptr_table_get (table, aig));
    p              = btor_hashptr_table_add (table, aig);
    p->data.as_int = ++M;
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
    if (!btor_aig_is_const (aig)) BTOR_PUSH_STACK (stack, aig);
  }
  for (i = naigs - 1; i >= 0; i--)
  {
    aig = aigs[i];
    if (!btor_aig_is_const (aig)) BTOR_PUSH_STACK (stack, aig);
  }

  while (!BTOR_EMPTY_STACK (stack))
  {
    aig = BTOR_POP_STACK (stack);

    if (aig)
    {
    CONTINUE_WITH_NON_ZERO_AIG:

      assert (!btor_aig_is_const (aig));
      aig = BTOR_REAL_ADDR_AIG (aig);

      if (!aig->mark) continue;

      aig->mark = 0;

      if (btor_aig_is_var (aig)) continue;

      BTOR_PUSH_STACK (stack, aig);
      BTOR_PUSH_STACK (stack, 0);

      right = btor_aig_get_right_child (amgr, aig);
      BTOR_PUSH_STACK (stack, right);

      aig = btor_aig_get_left_child (amgr, aig);
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
      assert (btor_aig_is_and (aig));

      p              = btor_hashptr_table_add (table, aig);
      p->data.as_int = ++M;
      assert (M > 0);
    }
  }

  A = M - I - L;

  BTOR_RELEASE_STACK (stack);

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

    if (!btor_aig_is_var (aig)) break;

    if (btor_hashptr_table_get (latches, aig)) continue;

    if (!binary) fprintf (file, "%d\n", 2 * p->data.as_int);

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
    assert (btor_aig_is_and (aig));

    left  = btor_aig_get_left_child (amgr, aig);
    right = btor_aig_get_right_child (amgr, aig);

    aig_id   = 2 * (unsigned) p->data.as_int;
    left_id  = aiger_encode_aig (table, left);
    right_id = aiger_encode_aig (table, right);

    if (left_id < right_id) BTOR_SWAP (int, left_id, right_id);

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
      if (!btor_aig_is_var (aig)) break;

      b = btor_hashptr_table_get (backannotation, aig);

      if (!b) continue;

      assert (b->key == aig);
      assert (b->data.as_str);
      //	  assert (p->data.as_int == i + l + 1);
      if (btor_hashptr_table_get (latches, aig))
        fprintf (file, "l%d %s\n", l++, b->data.as_str);
      else
        fprintf (file, "i%d %s\n", i++, b->data.as_str);
    }
  }

  btor_hashptr_table_delete (table);
  btor_hashptr_table_delete (latches);
}
