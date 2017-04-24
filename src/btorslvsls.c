/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015-2017 Aina Niemetz.
 *  Copyright (C) 2015 Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btorslvsls.h"
#include "btorbv.h"
#include "btorclone.h"
#include "btorcore.h"
#include "btormodel.h"
#include "btorslvpropsls.h"
#include "utils/btorexpiter.h"
#include "utils/btorhashint.h"
#include "utils/btorhashptr.h"
#include "utils/btormisc.h"
#include "utils/btornodemap.h"
#include "utils/btorutil.h"
#ifndef NBTORLOG
#include "btorprintmodel.h"
#endif
#include "btorabort.h"
#include "btordbg.h"
#include "btorlog.h"

#include <math.h>

/* same restart scheme as in Z3 */
#define BTOR_SLS_MAXSTEPS_CFACT 100 /* same as in Z3 (c4) */
#define BTOR_SLS_MAXSTEPS(i) \
  (BTOR_SLS_MAXSTEPS_CFACT * ((i) &1u ? 1 : 1 << ((i) >> 1)))

#define BTOR_SLS_SELECT_CFACT 20 /* same as in Z3 (c2) */

#define BTOR_SLS_PROB_SCORE_F 50 /* = 0.05 (same as in Z3 (sp)) */

/* choose move with one candidate rather than group-wise move
 * for random walk (prob=0.05) */
#define BTOR_SLS_PROB_SINGLE_VS_GW 50
/* randomize all candidates rather than one only (prob=0.5) */
#define BTOR_SLS_PROB_RAND_ALL_VS_ONE 500
/* start ranges from MSB rather than LSB (prob=0.5) */
#define BTOR_SLS_PROB_RANGE_MSB_VS_LSB 500
/* start segments from MSB rather than LSB (prob=0.5) */
#define BTOR_SLS_PROB_SEG_MSB_VS_LSB 500

/*------------------------------------------------------------------------*/

static double
compute_sls_score_formula (Btor *btor, BtorIntHashTable *score, bool *done)
{
  assert (btor);
  assert (score);

  double res, sc, weight;
  int32_t id;
  BtorSLSSolver *slv;
  BtorIntHashTableIterator it;

  slv = BTOR_SLS_SOLVER (btor);
  assert (slv);
  assert (slv->roots);
  assert (slv->weights);

  res = 0.0;
  if (done) *done = true;

  btor_init_int_hash_table_iterator (&it, slv->weights);
  while (btor_has_next_int_hash_table_iterator (&it))
  {
    weight =
        (double) ((BtorSLSConstrData *) slv->weights->data[it.cur_pos].as_ptr)
            ->weight;
    id = btor_next_int_hash_table_iterator (&it);
    sc = btor_get_int_hash_map (score, id)->as_dbl;
    assert (sc >= 0.0 && sc <= 1.0);
    if (done && sc < 1.0) *done = false;
    res += weight * sc;
  }
  return res;
}

static BtorNode *
select_candidate_constraint (Btor *btor, int nmoves)
{
  assert (btor);

  double score;
  int32_t id;
  BtorNode *res;
  BtorSLSSolver *slv;
  BtorIntHashTableIterator it;

  slv = BTOR_SLS_SOLVER (btor);
  assert (slv);
  assert (slv->roots);
  assert (slv->score);

  res = 0;

  if (btor_opt_get (btor, BTOR_OPT_SLS_USE_BANDIT))
  {
    double value, max_value;
    BtorSLSConstrData *d;

    max_value = 0.0;
    btor_init_int_hash_table_iterator (&it, slv->roots);
    while (btor_has_next_int_hash_table_iterator (&it))
    {
      id = btor_next_int_hash_table_iterator (&it);
      assert (!btor_is_bv_const_node (btor_get_node_by_id (btor, id))
              || !btor_bv_is_zero (
                     btor_model_get_bv (btor, btor_get_node_by_id (btor, id))));
      assert (btor_contains_int_hash_map (slv->weights, id));
      d = btor_get_int_hash_map (slv->weights, id)->as_ptr;
      assert (d);
      assert (btor_contains_int_hash_map (slv->score, id));
      score = btor_get_int_hash_map (slv->score, id)->as_dbl;
      assert (score < 1.0);
      value = score + BTOR_SLS_SELECT_CFACT * sqrt (log (d->selected) / nmoves);
      if (!res || value > max_value)
      {
        res       = btor_get_node_by_id (btor, id);
        max_value = value;
        d->selected += 1;
      }
    }
  }
  else
  {
    uint32_t r;
    BtorNode *cur;
    BtorNodePtrStack stack;

    BTOR_INIT_STACK (btor->mm, stack);
    btor_init_int_hash_table_iterator (&it, slv->roots);
    while (btor_has_next_int_hash_table_iterator (&it))
    {
      id  = btor_next_int_hash_table_iterator (&it);
      cur = btor_get_node_by_id (btor, id);
      assert (!btor_is_bv_const_node (cur)
              || !btor_bv_is_zero (btor_model_get_bv (btor, cur)));
      assert (btor_contains_int_hash_map (slv->score, id));
      score = btor_get_int_hash_map (slv->score, id)->as_dbl;
      assert (score < 1.0);
      BTOR_PUSH_STACK (stack, cur);
    }
    assert (BTOR_COUNT_STACK (stack));
    r   = btor_pick_rand_rng (&btor->rng, 0, BTOR_COUNT_STACK (stack) - 1);
    res = stack.start[r];
    BTOR_RELEASE_STACK (stack);
  }

  assert (res);

  BTORLOG (1, "");
  BTORLOG (1, "*** select candidate constraint: %s", node2string (res));

  return res;
}

static void
select_candidates (Btor *btor, BtorNode *root, BtorNodePtrStack *candidates)
{
  assert (btor);
  assert (root);
  assert (candidates);

  int i;
  BtorNode *cur, *real_cur, *e;
  BtorNodePtrStack stack, controlling;
  const BtorBitVector *bv;
  BtorIntHashTable *mark;
  BtorMemMgr *mm;

  BTORLOG (1, "");
  BTORLOG (1, "*** select candidates");

  mm = btor->mm;
  BTOR_INIT_STACK (mm, stack);
  BTOR_INIT_STACK (mm, controlling);

  BTOR_RESET_STACK (*candidates);
  mark = btor_new_int_hash_table (mm);

  BTOR_PUSH_STACK (stack, root);
  while (!BTOR_EMPTY_STACK (stack))
  {
    cur      = BTOR_POP_STACK (stack);
    real_cur = BTOR_REAL_ADDR_NODE (cur);
    if (btor_contains_int_hash_table (mark, real_cur->id)) continue;
    btor_add_int_hash_table (mark, real_cur->id);

    if (btor_is_bv_var_node (real_cur))
    {
      BTOR_PUSH_STACK (*candidates, real_cur);
      BTORLOG (1, "  %s", node2string (real_cur));
      continue;
    }

    /* push children */
    if (btor_opt_get (btor, BTOR_OPT_SLS_JUST) && btor_is_and_node (real_cur)
        && btor_get_exp_width (btor, real_cur) == 1)
    {
      bv = btor_model_get_bv (btor, real_cur);
      if (!btor_bv_is_zero (bv)) /* push all */
        goto PUSH_CHILDREN;
      else /* push one controlling input */
      {
        BTOR_RESET_STACK (controlling);
        for (i = 0; i < real_cur->arity; i++)
        {
          e = real_cur->e[i];
          if (btor_bv_is_zero (btor_model_get_bv (btor, e)))
            BTOR_PUSH_STACK (controlling, real_cur->e[i]);
        }
        assert (BTOR_COUNT_STACK (controlling));
        BTOR_PUSH_STACK (
            stack,
            BTOR_PEEK_STACK (
                controlling,
                btor_pick_rand_rng (
                    &btor->rng, 0, BTOR_COUNT_STACK (controlling) - 1)));
      }
    }
    else
    {
    PUSH_CHILDREN:
      for (i = 0; i < real_cur->arity; i++)
        BTOR_PUSH_STACK (stack, real_cur->e[i]);
    }
  }

  BTOR_RELEASE_STACK (stack);
  BTOR_RELEASE_STACK (controlling);
  btor_delete_int_hash_table (mark);
}

#if 0
static void *
same_node (BtorMemMgr * mm, const void * map, const void * key)
{
  assert (mm);
  assert (key);

  (void) mm;
  (void) map;
  return (BtorNode *) key;
}
#endif

static inline void
update_assertion_weights (Btor *btor)
{
  assert (btor);

  int32_t id;
  BtorSLSConstrData *d;
  BtorIntHashTableIterator it;
  BtorSLSSolver *slv;

  slv = BTOR_SLS_SOLVER (btor);

  if (btor_pick_with_prob_rng (&btor->rng, BTOR_SLS_PROB_SCORE_F))
  {
    /* decrease the weight of all satisfied assertions */
    btor_init_int_hash_table_iterator (&it, slv->weights);
    while (btor_has_next_int_hash_table_iterator (&it))
    {
      d  = (BtorSLSConstrData *) slv->weights->data[it.cur_pos].as_ptr;
      id = btor_next_int_hash_table_iterator (&it);
      assert (btor_contains_int_hash_table (slv->score, id));
      if (btor_get_int_hash_map (slv->score, id)->as_dbl == 0.0) continue;
      if (d->weight > 1) d->weight -= 1;
    }
  }
  else
  {
    /* increase the weight of all unsatisfied assertions */
    btor_init_int_hash_table_iterator (&it, slv->weights);
    while (btor_has_next_int_hash_table_iterator (&it))
    {
      d  = (BtorSLSConstrData *) slv->weights->data[it.cur_pos].as_ptr;
      id = btor_next_int_hash_table_iterator (&it);
      assert (btor_contains_int_hash_table (slv->score, id));
      if (btor_get_int_hash_map (slv->score, id)->as_dbl == 1.0) continue;
      d->weight += 1;
    }
  }
}

static inline double
try_move (Btor *btor,
          BtorIntHashTable *bv_model,
          BtorIntHashTable *score,
          BtorIntHashTable *cans,
          bool *done)
{
  assert (btor);
  assert (bv_model);
  assert (score);
  assert (cans);
  assert (cans->count);
  assert (done);

  BtorSLSSolver *slv;

  slv = BTOR_SLS_SOLVER (btor);
  assert (slv);
  if (slv->nflips && slv->stats.flips >= slv->nflips)
  {
    slv->terminate = true;
    return 0.0;
  }
  slv->stats.flips += 1;

#ifndef NBTORLOG
  char *a;
  BtorNode *can;
  BtorBitVector *prev_ass, *new_ass;
  BtorIntHashTableIterator iit;

  BTORLOG (2, "");
  BTORLOG (2, "  * try move:");
  btor_init_int_hash_table_iterator (&iit, cans);
  while (btor_has_next_int_hash_table_iterator (&iit))
  {
    new_ass = (BtorBitVector *) cans->data[iit.cur_pos].as_ptr;
    can = btor_get_node_by_id (btor, btor_next_int_hash_table_iterator (&iit));
    prev_ass = (BtorBitVector *) btor_model_get_bv (btor, can);
    BTORLOG (2,
             "      candidate: %s%s",
             BTOR_IS_REGULAR_NODE (can) ? "" : "-",
             node2string (can));
    a = btor_bv_to_char (btor->mm, prev_ass);
    BTORLOG (2, "        prev. assignment: %s", a);
    btor_freestr (btor->mm, a);
    a = btor_bv_to_char (btor->mm, new_ass);
    BTORLOG (2, "        new   assignment: %s", a);
    btor_freestr (btor->mm, a);
  }
#endif

  btor_propsls_update_cone (btor,
                            bv_model,
                            slv->roots,
                            score,
                            cans,
                            false,
                            &slv->stats.updates,
                            &slv->time.update_cone,
                            &slv->time.update_cone_reset,
                            &slv->time.update_cone_model_gen,
                            &slv->time.update_cone_compute_score);

  return compute_sls_score_formula (btor, score, done);
}

static int
cmp_sls_moves_qsort (const void *move1, const void *move2)
{
  BtorSLSMove *m1, *m2;

  m1 = *((BtorSLSMove **) move1);
  m2 = *((BtorSLSMove **) move2);
  if (m1->sc > m2->sc) return 1;
  if (m1->sc < m2->sc) return -1;
  return 0;
}

#define BTOR_SLS_DELETE_CANS(cans)                                          \
  do                                                                        \
  {                                                                         \
    btor_init_int_hash_table_iterator (&iit, cans);                         \
    while (btor_has_next_int_hash_table_iterator (&iit))                    \
    {                                                                       \
      assert (cans->data[iit.cur_pos].as_ptr);                              \
      btor_bv_free (btor->mm,                                               \
                    btor_next_data_int_hash_table_iterator (&iit)->as_ptr); \
    }                                                                       \
    btor_delete_int_hash_map (cans);                                        \
  } while (0)

#define BTOR_SLS_SELECT_MOVE_CHECK_SCORE(sc)                              \
  do                                                                      \
  {                                                                       \
    if (done                                                              \
        || (sls_strat != BTOR_SLS_STRAT_RAND_WALK                         \
            && ((sc) > slv->max_score                                     \
                || (sls_strat == BTOR_SLS_STRAT_BEST_SAME_MOVE            \
                    && (sc) == slv->max_score))))                         \
    {                                                                     \
      slv->max_score = (sc);                                              \
      slv->max_move  = mk;                                                \
      slv->max_gw    = gw;                                                \
      if (slv->max_cans->count)                                           \
      {                                                                   \
        btor_init_int_hash_table_iterator (&iit, slv->max_cans);          \
        while (btor_has_next_int_hash_table_iterator (&iit))              \
        {                                                                 \
          assert (slv->max_cans->data[iit.cur_pos].as_ptr);               \
          btor_bv_free (                                                  \
              btor->mm,                                                   \
              btor_next_data_int_hash_table_iterator (&iit)->as_ptr);     \
        }                                                                 \
      }                                                                   \
      btor_delete_int_hash_map (slv->max_cans);                           \
      slv->max_cans = cans;                                               \
      if (done || sls_strat == BTOR_SLS_STRAT_FIRST_BEST_MOVE) goto DONE; \
    }                                                                     \
    else if (sls_strat == BTOR_SLS_STRAT_RAND_WALK)                       \
    {                                                                     \
      BTOR_NEW (btor->mm, m);                                             \
      m->cans = cans;                                                     \
      m->sc   = (sc);                                                     \
      BTOR_PUSH_STACK (slv->moves, m);                                    \
      slv->sum_score += m->sc;                                            \
    }                                                                     \
    else                                                                  \
    {                                                                     \
      BTOR_SLS_DELETE_CANS (cans);                                        \
    }                                                                     \
  } while (0)

static inline bool
select_inc_dec_not_move (Btor *btor,
                         BtorBitVector *(*fun) (BtorMemMgr *,
                                                const BtorBitVector *),
                         BtorNodePtrStack *candidates,
                         int gw)
{
  int32_t i;
  uint32_t sls_strat;
  bool done;
  double sc;
  BtorSLSMove *m;
  BtorSLSMoveKind mk;
  BtorBitVector *ass, *max_neigh;
  BtorNode *can;
  BtorIntHashTable *cans, *bv_model, *score;
  BtorIntHashTableIterator iit;
  BtorSLSSolver *slv;

  done      = false;
  slv       = BTOR_SLS_SOLVER (btor);
  sls_strat = btor_opt_get (btor, BTOR_OPT_SLS_STRATEGY);

  if (fun == btor_bv_inc)
    mk = BTOR_SLS_MOVE_INC;
  else if (fun == btor_bv_dec)
    mk = BTOR_SLS_MOVE_DEC;
  else
  {
    assert (fun == btor_bv_not);
    mk = BTOR_SLS_MOVE_NOT;
  }

  bv_model = btor_model_clone_bv (btor, btor->bv_model, true);
  score =
      btor_clone_int_hash_map (btor->mm, slv->score, btor_clone_data_as_dbl, 0);

  cans = btor_new_int_hash_map (btor->mm);

  for (i = 0; i < BTOR_COUNT_STACK (*candidates); i++)
  {
    can = BTOR_PEEK_STACK (*candidates, i);
    assert (can);
    assert (BTOR_IS_REGULAR_NODE (can));

    ass = (BtorBitVector *) btor_model_get_bv (btor, can);
    assert (ass);

    max_neigh = btor_contains_int_hash_map (slv->max_cans, can->id)
                    ? btor_get_int_hash_map (slv->max_cans, can->id)->as_ptr
                    : 0;

    btor_add_int_hash_map (cans, can->id)->as_ptr =
        btor_opt_get (btor, BTOR_OPT_SLS_MOVE_INC_MOVE_TEST) && max_neigh
            ? fun (btor->mm, max_neigh)
            : fun (btor->mm, ass);
  }

  sc = try_move (btor, bv_model, score, cans, &done);
  if (slv->terminate)
  {
    BTOR_SLS_DELETE_CANS (cans);
    goto DONE;
  }
  BTOR_SLS_SELECT_MOVE_CHECK_SCORE (sc);

DONE:
  btor_model_delete_bv (btor, &bv_model);
  btor_delete_int_hash_map (score);
  return done;
}

static inline bool
select_flip_move (Btor *btor, BtorNodePtrStack *candidates, int gw)
{
  int32_t i, n_endpos;
  uint32_t pos, cpos, sls_strat;
  bool done = false;
  double sc;
  BtorSLSMove *m;
  BtorSLSMoveKind mk;
  BtorBitVector *ass, *max_neigh;
  BtorNode *can;
  BtorIntHashTable *cans, *bv_model, *score;
  BtorIntHashTableIterator iit;
  BtorSLSSolver *slv;

  slv       = BTOR_SLS_SOLVER (btor);
  sls_strat = btor_opt_get (btor, BTOR_OPT_SLS_STRATEGY);

  mk = BTOR_SLS_MOVE_FLIP;

  bv_model = btor_model_clone_bv (btor, btor->bv_model, true);
  score =
      btor_clone_int_hash_map (btor->mm, slv->score, btor_clone_data_as_dbl, 0);

  for (pos = 0, n_endpos = 0; n_endpos < BTOR_COUNT_STACK (*candidates); pos++)
  {
    cans = btor_new_int_hash_map (btor->mm);

    for (i = 0; i < BTOR_COUNT_STACK (*candidates); i++)
    {
      can = BTOR_PEEK_STACK (*candidates, i);
      assert (BTOR_IS_REGULAR_NODE (can));
      assert (can);

      ass = (BtorBitVector *) btor_model_get_bv (btor, can);
      assert (ass);

      max_neigh = btor_contains_int_hash_map (slv->max_cans, can->id)
                      ? btor_get_int_hash_map (slv->max_cans, can->id)->as_ptr
                      : 0;

      if (pos == ass->width - 1) n_endpos += 1;
      cpos = pos % ass->width;

      btor_add_int_hash_map (cans, can->id)->as_ptr =
          btor_opt_get (btor, BTOR_OPT_SLS_MOVE_INC_MOVE_TEST) && max_neigh
              ? btor_bv_flipped_bit (btor->mm, max_neigh, cpos)
              : btor_bv_flipped_bit (btor->mm, ass, cpos);
    }

    sc = try_move (btor, bv_model, score, cans, &done);
    if (slv->terminate)
    {
      BTOR_SLS_DELETE_CANS (cans);
      goto DONE;
    }
    BTOR_SLS_SELECT_MOVE_CHECK_SCORE (sc);
  }

DONE:
  btor_model_delete_bv (btor, &bv_model);
  btor_delete_int_hash_map (score);
  return done;
}

static inline bool
select_flip_range_move (Btor *btor, BtorNodePtrStack *candidates, int gw)
{
  int32_t i, n_endpos;
  uint32_t up, cup, clo, sls_strat;
  bool done = false;
  double sc;
  BtorSLSMove *m;
  BtorSLSMoveKind mk;
  BtorBitVector *ass, *max_neigh;
  BtorNode *can;
  BtorIntHashTable *cans, *bv_model, *score;
  BtorIntHashTableIterator iit;
  BtorSLSSolver *slv;

  slv       = BTOR_SLS_SOLVER (btor);
  sls_strat = btor_opt_get (btor, BTOR_OPT_SLS_STRATEGY);

  mk = BTOR_SLS_MOVE_FLIP_RANGE;

  bv_model = btor_model_clone_bv (btor, btor->bv_model, true);
  score =
      btor_clone_int_hash_map (btor->mm, slv->score, btor_clone_data_as_dbl, 0);

  for (up = 1, n_endpos = 0; n_endpos < BTOR_COUNT_STACK (*candidates);
       up = 2 * up + 1)
  {
    cans = btor_new_int_hash_map (btor->mm);

    for (i = 0; i < BTOR_COUNT_STACK (*candidates); i++)
    {
      can = BTOR_PEEK_STACK (*candidates, i);
      assert (can);
      assert (BTOR_IS_REGULAR_NODE (can));

      ass = (BtorBitVector *) btor_model_get_bv (btor, can);
      assert (ass);

      max_neigh = btor_contains_int_hash_map (slv->max_cans, can->id)
                      ? btor_get_int_hash_map (slv->max_cans, can->id)->as_ptr
                      : 0;

      clo = 0;
      cup = up;
      if (up >= ass->width)
      {
        if ((up - 1) / 2 < ass->width) n_endpos += 1;
        cup = ass->width - 1;
      }

      /* range from MSB rather than LSB with given prob */
      if (btor_pick_with_prob_rng (&btor->rng, BTOR_SLS_PROB_RANGE_MSB_VS_LSB))
      {
        clo = ass->width - 1 - cup;
        cup = ass->width - 1;
      }

      btor_add_int_hash_map (cans, can->id)->as_ptr =
          btor_opt_get (btor, BTOR_OPT_SLS_MOVE_INC_MOVE_TEST) && max_neigh
              ? btor_bv_flipped_bit_range (btor->mm, max_neigh, cup, clo)
              : btor_bv_flipped_bit_range (btor->mm, ass, cup, clo);
    }

    sc = try_move (btor, bv_model, score, cans, &done);
    if (slv->terminate)
    {
      BTOR_SLS_DELETE_CANS (cans);
      goto DONE;
    }
    BTOR_SLS_SELECT_MOVE_CHECK_SCORE (sc);
  }

DONE:
  btor_model_delete_bv (btor, &bv_model);
  btor_delete_int_hash_map (score);
  return done;
}

static inline bool
select_flip_segment_move (Btor *btor, BtorNodePtrStack *candidates, int gw)
{
  int32_t i, ctmp, n_endpos;
  uint32_t lo, clo, up, cup, seg, sls_strat;
  bool done = false;
  double sc;
  BtorSLSMove *m;
  BtorSLSMoveKind mk;
  BtorBitVector *ass, *max_neigh;
  BtorNode *can;
  BtorIntHashTable *cans, *bv_model, *score;
  BtorIntHashTableIterator iit;
  BtorSLSSolver *slv;

  slv       = BTOR_SLS_SOLVER (btor);
  sls_strat = btor_opt_get (btor, BTOR_OPT_SLS_STRATEGY);

  mk = BTOR_SLS_MOVE_FLIP_SEGMENT;

  bv_model = btor_model_clone_bv (btor, btor->bv_model, true);
  score =
      btor_clone_int_hash_map (btor->mm, slv->score, btor_clone_data_as_dbl, 0);

  for (seg = 2; seg <= 8; seg <<= 1)
  {
    for (lo = 0, up = seg - 1, n_endpos = 0;
         n_endpos < BTOR_COUNT_STACK (*candidates);
         lo += seg, up += seg)
    {
      cans = btor_new_int_hash_map (btor->mm);

      for (i = 0; i < BTOR_COUNT_STACK (*candidates); i++)
      {
        can = BTOR_PEEK_STACK (*candidates, i);
        assert (can);
        assert (BTOR_IS_REGULAR_NODE (can));

        ass = (BtorBitVector *) btor_model_get_bv (btor, can);
        assert (ass);

        max_neigh = btor_contains_int_hash_map (slv->max_cans, can->id)
                        ? btor_get_int_hash_map (slv->max_cans, can->id)->as_ptr
                        : 0;

        clo = lo;
        cup = up;

        if (up >= ass->width)
        {
          if (up - seg < ass->width) n_endpos += 1;
          cup = ass->width - 1;
        }

        if (lo >= ass->width - 1) clo = ass->width < seg ? 0 : ass->width - seg;

        /* range from MSB rather than LSB with given prob */
        if (btor_pick_with_prob_rng (&btor->rng, BTOR_SLS_PROB_SEG_MSB_VS_LSB))
        {
          ctmp = clo;
          clo  = ass->width - 1 - cup;
          cup  = ass->width - 1 - ctmp;
        }

        btor_add_int_hash_map (cans, can->id)->as_ptr =
            btor_opt_get (btor, BTOR_OPT_SLS_MOVE_INC_MOVE_TEST) && max_neigh
                ? btor_bv_flipped_bit_range (btor->mm, max_neigh, cup, clo)
                : btor_bv_flipped_bit_range (btor->mm, ass, cup, clo);
      }

      sc = try_move (btor, bv_model, score, cans, &done);
      if (slv->terminate)
      {
        BTOR_SLS_DELETE_CANS (cans);
        goto DONE;
      }
      BTOR_SLS_SELECT_MOVE_CHECK_SCORE (sc);
    }
  }

DONE:
  btor_model_delete_bv (btor, &bv_model);
  btor_delete_int_hash_map (score);
  return done;
}

static inline bool
select_rand_range_move (Btor *btor, BtorNodePtrStack *candidates, int gw)
{
  double sc, rand_max_score = -1.0;
  int32_t i, n_endpos;
  uint32_t up, cup, clo, sls_strat;
  bool done;
  BtorSLSMove *m;
  BtorSLSMoveKind mk;
  BtorBitVector *ass;
  BtorNode *can;
  BtorIntHashTable *cans, *bv_model, *score;
  BtorIntHashTableIterator iit;
  BtorSLSSolver *slv;

  done      = false;
  slv       = BTOR_SLS_SOLVER (btor);
  sls_strat = btor_opt_get (btor, BTOR_OPT_SLS_STRATEGY);

  mk = BTOR_SLS_MOVE_RAND;

  bv_model = btor_model_clone_bv (btor, btor->bv_model, true);
  score =
      btor_clone_int_hash_map (btor->mm, slv->score, btor_clone_data_as_dbl, 0);

  for (up = 1, n_endpos = 0; n_endpos < BTOR_COUNT_STACK (*candidates);
       up = 2 * up + 1)
  {
    cans = btor_new_int_hash_map (btor->mm);

    for (i = 0; i < BTOR_COUNT_STACK (*candidates); i++)
    {
      can = BTOR_PEEK_STACK (*candidates, i);
      assert (can);
      assert (BTOR_IS_REGULAR_NODE (can));

      ass = (BtorBitVector *) btor_model_get_bv (btor, can);
      assert (ass);

      clo = 0;
      cup = up;
      if (up >= ass->width)
      {
        if ((up - 1) / 2 < ass->width) n_endpos += 1;
        cup = ass->width - 1;
      }

      /* range from MSB rather than LSB with given prob */
      if (btor_pick_with_prob_rng (&btor->rng, BTOR_SLS_PROB_RANGE_MSB_VS_LSB))
      {
        clo = ass->width - 1 - cup;
        cup = ass->width - 1;
      }
      btor_add_int_hash_map (cans, can->id)->as_ptr =
          btor_bv_new_random_bit_range (
              btor->mm, &btor->rng, ass->width, cup, clo);
    }

    sc = try_move (btor, bv_model, score, cans, &done);
    if (slv->terminate)
    {
      BTOR_SLS_DELETE_CANS (cans);
      goto DONE;
    }
    if (rand_max_score == -1.0 || sc > rand_max_score)
    {
      /* reset, use current */
      slv->max_score = -1.0;
      rand_max_score = sc;
    }
    BTOR_SLS_SELECT_MOVE_CHECK_SCORE (sc);
  }

DONE:
  btor_model_delete_bv (btor, &bv_model);
  btor_delete_int_hash_map (score);
  return done;
}

static inline bool
select_move_aux (Btor *btor, BtorNodePtrStack *candidates, int gw)
{
  assert (btor);
  assert (candidates);
  assert (gw >= 0);

  BtorSLSMoveKind mk;
  BtorSLSSolver *slv;
  bool done = false;

  slv = BTOR_SLS_SOLVER (btor);

  for (mk = 0; mk < BTOR_SLS_MOVE_DONE; mk++)
  {
    if (slv->nflips && slv->stats.flips >= slv->nflips)
    {
      slv->terminate = true;
      break;
    }

    switch (mk)
    {
      case BTOR_SLS_MOVE_INC:
        if ((done =
                 select_inc_dec_not_move (btor, btor_bv_inc, candidates, gw)))
          return done;
        break;

      case BTOR_SLS_MOVE_DEC:
        if ((done =
                 select_inc_dec_not_move (btor, btor_bv_dec, candidates, gw)))
          return done;
        break;

      case BTOR_SLS_MOVE_NOT:
        if ((done =
                 select_inc_dec_not_move (btor, btor_bv_not, candidates, gw)))
          return done;
        break;

      case BTOR_SLS_MOVE_FLIP_RANGE:
        if (!btor_opt_get (btor, BTOR_OPT_SLS_MOVE_RANGE)) continue;
        if ((done = select_flip_range_move (btor, candidates, gw))) return done;
        break;

      case BTOR_SLS_MOVE_FLIP_SEGMENT:
        if (!btor_opt_get (btor, BTOR_OPT_SLS_MOVE_SEGMENT)) continue;
        if ((done = select_flip_segment_move (btor, candidates, gw)))
          return done;
        break;

      default:
        assert (mk == BTOR_SLS_MOVE_FLIP);
        if ((done = select_flip_move (btor, candidates, gw))) return done;
    }
  }

  return done;
}

static inline void
select_move (Btor *btor, BtorNodePtrStack *candidates)
{
  assert (btor);
  assert (candidates);

  int32_t i, r;
  bool randomizeall;
  bool done;
  double rd, sum;
  BtorNode *can;
  BtorBitVector *neigh;
  BtorNodePtrStack cans;
  BtorSLSMove *m;
  BtorIntHashTableIterator iit;
  BtorSLSSolver *slv;

  slv = BTOR_SLS_SOLVER (btor);
  assert (slv->max_cans);
  assert (!slv->max_cans->count);

  BTOR_INIT_STACK (btor->mm, cans);
  /* one after another */
  for (i = 0; i < BTOR_COUNT_STACK (*candidates); i++)
  {
    can = BTOR_PEEK_STACK (*candidates, i);
    assert (can);
    BTOR_PUSH_STACK (cans, can);

    if ((done = select_move_aux (btor, &cans, 0))) goto DONE;
    if (slv->terminate) goto DONE;

    BTOR_RESET_STACK (cans);
  }

  /* groupwise */
  if (btor_opt_get (btor, BTOR_OPT_SLS_MOVE_GW)
      && BTOR_COUNT_STACK (*candidates) > 1)
  {
    if ((done = select_move_aux (btor, candidates, 1))) goto DONE;
    if (slv->terminate) goto DONE;
  }

  /* select probabilistic random walk move
   * (weighted by score; the higher the score, the higher the probability
   * that a move gets chosen) */
  if (btor_opt_get (btor, BTOR_OPT_SLS_STRATEGY) == BTOR_SLS_STRAT_RAND_WALK)
  {
    assert (slv->max_cans->count == 0);
    assert (BTOR_COUNT_STACK (slv->moves));

    qsort (slv->moves.start,
           BTOR_COUNT_STACK (slv->moves),
           sizeof (BtorSLSMove *),
           cmp_sls_moves_qsort);

    rd = btor_pick_rand_dbl_rng (&btor->rng, 0, slv->sum_score);
    m  = BTOR_PEEK_STACK (slv->moves, 0);
    for (i = 0, sum = 0; i < BTOR_COUNT_STACK (slv->moves); i++)
    {
      sum += m->sc;
      if (sum > rd) break;
      m = BTOR_PEEK_STACK (slv->moves, i);
    }

    slv->max_gw   = m->cans->count > 1;
    slv->max_move = BTOR_SLS_MOVE_RAND_WALK;
    btor_init_int_hash_table_iterator (&iit, m->cans);
    while (btor_has_next_int_hash_table_iterator (&iit))
    {
      neigh = btor_bv_copy (btor->mm, m->cans->data[iit.cur_pos].as_ptr);
      can =
          btor_get_node_by_id (btor, btor_next_int_hash_table_iterator (&iit));
      assert (BTOR_IS_REGULAR_NODE (can));
      assert (neigh);
      btor_add_int_hash_map (slv->max_cans, can->id)->as_ptr = neigh;
    }
  }

  if (slv->max_cans->count == 0)
  {
    assert (slv->max_move == BTOR_SLS_MOVE_DONE);

    /* randomize if no best move was found */
    randomizeall = btor_opt_get (btor, BTOR_OPT_SLS_MOVE_RAND_ALL)
                       ? btor_pick_with_prob_rng (&btor->rng,
                                                  BTOR_SLS_PROB_RAND_ALL_VS_ONE)
                       : false;

    if (randomizeall)
    {
      slv->max_gw   = 1;
      slv->max_move = BTOR_SLS_MOVE_RAND;

      for (r = 0; r <= BTOR_COUNT_STACK (*candidates) - 1; r++)
      {
        can = BTOR_PEEK_STACK (*candidates, r);
        assert (BTOR_IS_REGULAR_NODE (can));
        if (btor_get_exp_width (btor, can) == 1)
          neigh = btor_bv_flipped_bit (
              btor->mm, (BtorBitVector *) btor_model_get_bv (btor, can), 0);
        else
          neigh = btor_bv_new_random (
              btor->mm, &btor->rng, btor_get_exp_width (btor, can));

        btor_add_int_hash_map (slv->max_cans, can->id)->as_ptr = neigh;
      }
    }
    else
    {
      slv->max_gw   = 0;
      slv->max_move = BTOR_SLS_MOVE_RAND;

      can = BTOR_PEEK_STACK (
          *candidates,
          btor_pick_rand_rng (
              &btor->rng, 0, BTOR_COUNT_STACK (*candidates) - 1));
      assert (BTOR_IS_REGULAR_NODE (can));

      if (btor_get_exp_width (btor, can) == 1)
      {
        neigh = btor_bv_flipped_bit (
            btor->mm, (BtorBitVector *) btor_model_get_bv (btor, can), 0);
        btor_add_int_hash_map (slv->max_cans, can->id)->as_ptr = neigh;
      }
      /* pick neighbor with randomized bit range (best guess) */
      else if (btor_opt_get (btor, BTOR_OPT_SLS_MOVE_RAND_RANGE))
      {
        assert (!BTOR_COUNT_STACK (cans));
        BTOR_PUSH_STACK (cans, can);
        select_rand_range_move (btor, &cans, 0);
        BTOR_RESET_STACK (cans);
        assert (slv->max_cans->count == 1);
      }
      else
      {
        neigh = btor_bv_new_random (
            btor->mm, &btor->rng, btor_get_exp_width (btor, can));
        btor_add_int_hash_map (slv->max_cans, can->id)->as_ptr = neigh;
      }

      assert (!slv->max_gw);
      assert (slv->max_move == BTOR_SLS_MOVE_RAND);
    }
    assert (slv->max_cans->count);
  }

DONE:
  BTOR_RELEASE_STACK (cans);
  while (!BTOR_EMPTY_STACK (slv->moves))
  {
    m = BTOR_POP_STACK (slv->moves);
    btor_init_int_hash_table_iterator (&iit, m->cans);
    while (btor_has_next_int_hash_table_iterator (&iit))
      btor_bv_free (btor->mm,
                    btor_next_data_int_hash_table_iterator (&iit)->as_ptr);
    btor_delete_int_hash_map (m->cans);
    BTOR_DELETE (btor->mm, m);
  }
}

static inline void
select_random_move (Btor *btor, BtorNodePtrStack *candidates)
{
  assert (btor);
  assert (candidates);

  int i;
  uint32_t r, up, lo;
  BtorSLSMoveKind mk;
  BtorNodePtrStack cans, *pcans;
  BtorNode *can;
  BtorBitVector *ass, *neigh;
  BtorSLSSolver *slv;

  slv = BTOR_SLS_SOLVER (btor);
  assert (slv->max_cans);
  assert (!slv->max_cans->count);

  BTOR_INIT_STACK (btor->mm, cans);

  slv->max_move = BTOR_SLS_MOVE_RAND_WALK;

  /* select candidate(s) */
  if (btor_opt_get (btor, BTOR_OPT_SLS_MOVE_GW)
      && btor_pick_with_prob_rng (&btor->rng, BTOR_SLS_PROB_SINGLE_VS_GW))
  {
    pcans       = candidates;
    slv->max_gw = 1;
  }
  else
  {
    BTOR_PUSH_STACK (
        cans,
        BTOR_PEEK_STACK (
            *candidates,
            btor_pick_rand_rng (
                &btor->rng, 0, BTOR_COUNT_STACK (*candidates) - 1)));
    pcans       = &cans;
    slv->max_gw = 0;
  }

  /* select neighbor(s) */
  for (i = 0; i < BTOR_COUNT_STACK (*pcans); i++)
  {
    can = BTOR_PEEK_STACK ((*pcans), i);
    assert (BTOR_IS_REGULAR_NODE (can));
    ass = (BtorBitVector *) btor_model_get_bv (btor, can);
    assert (ass);

    r = btor_pick_rand_rng (
        &btor->rng, 0, BTOR_SLS_MOVE_DONE - 1 + ass->width - 1);

    if (r < ass->width)
      mk = BTOR_SLS_MOVE_FLIP;
    else
      mk = (BtorSLSMoveKind) r - ass->width + 1;
    assert (mk >= 0);

    if ((!btor_opt_get (btor, BTOR_OPT_SLS_MOVE_SEGMENT)
         && mk == BTOR_SLS_MOVE_FLIP_SEGMENT)
        || (!btor_opt_get (btor, BTOR_OPT_SLS_MOVE_RANGE)
            && mk == BTOR_SLS_MOVE_FLIP_RANGE))
    {
      mk = BTOR_SLS_MOVE_FLIP;
    }

    switch (mk)
    {
      case BTOR_SLS_MOVE_INC: neigh = btor_bv_inc (btor->mm, ass); break;
      case BTOR_SLS_MOVE_DEC: neigh = btor_bv_dec (btor->mm, ass); break;
      case BTOR_SLS_MOVE_NOT: neigh = btor_bv_not (btor->mm, ass); break;
      case BTOR_SLS_MOVE_FLIP_RANGE:
        up = btor_pick_rand_rng (
            &btor->rng, ass->width > 1 ? 1 : 0, ass->width - 1);
        neigh = btor_bv_flipped_bit_range (btor->mm, ass, up, 0);
        break;
      case BTOR_SLS_MOVE_FLIP_SEGMENT:
        lo = btor_pick_rand_rng (&btor->rng, 0, ass->width - 1);
        up = btor_pick_rand_rng (
            &btor->rng, lo < ass->width - 1 ? lo + 1 : lo, ass->width - 1);
        neigh = btor_bv_flipped_bit_range (btor->mm, ass, up, lo);
        break;
      default:
        assert (mk == BTOR_SLS_MOVE_FLIP);
        neigh = btor_bv_flipped_bit (
            btor->mm, ass, btor_pick_rand_rng (&btor->rng, 0, ass->width - 1));
        break;
    }

    btor_add_int_hash_map (slv->max_cans, can->id)->as_ptr = neigh;
  }

  BTOR_RELEASE_STACK (cans);
}

/*------------------------------------------------------------------------*/

static int32_t
move (Btor *btor, uint32_t nmoves)
{
  assert (btor);

  uint32_t nprops, nsls;
  int32_t res;
  BtorNode *constr, *can;
  BtorNodePtrStack candidates;
  BtorIntHashTableIterator iit;
  BtorSLSSolver *slv;
  BtorBitVector *neigh;

  BTORLOG (1, "");
  BTORLOG (1, "*** move");

  BTOR_INIT_STACK (btor->mm, candidates);

  slv = BTOR_SLS_SOLVER (btor);
  assert (!slv->max_cans);
  assert (slv->roots->count);

  constr = select_candidate_constraint (btor, nmoves);

  slv->max_cans = btor_new_int_hash_map (btor->mm);

  res = 1;

  nprops = btor_opt_get (btor, BTOR_OPT_SLS_MOVE_PROP_N_PROP);
  nsls   = btor_opt_get (btor, BTOR_OPT_SLS_MOVE_PROP_N_SLS);

  /* Always perform propagation moves first, i.e. perform moves
   * with ratio nprops:nsls of propagation to sls moves */
  if (btor_opt_get (btor, BTOR_OPT_SLS_STRATEGY) == BTOR_SLS_STRAT_ALWAYS_PROP
      || (btor_opt_get (btor, BTOR_OPT_SLS_MOVE_PROP)
          && slv->npropmoves < nprops))
  {
    slv->npropmoves += 1;
    /* Select neighbor by propagating assignments from a given candidate
     * constraint (which is forced to be true) downwards. A downward path
     * is chosen via justification. If a non-recoverable conflict is
     * encountered, no move is performed. */
    slv->max_move = BTOR_SLS_MOVE_PROP;
    slv->stats.props +=
        btor_propsls_select_move_prop (btor, constr, &can, &neigh);
    if (can)
    {
      assert (neigh);
      btor_add_int_hash_map (slv->max_cans, BTOR_REAL_ADDR_NODE (can)->id)
          ->as_ptr = neigh;
    }
    else /* recovery move */
    {
      slv->stats.move_prop_non_rec_conf += 1;
      /* force random walk if prop move fails */
      if (btor_opt_get (btor, BTOR_OPT_SLS_MOVE_PROP_FORCE_RW))
      {
        select_candidates (btor, constr, &candidates);
        /* root is const false -> unsat */
        if (!BTOR_COUNT_STACK (candidates))
        {
          res = 0;
          goto DONE;
        }

        goto SLS_MOVE_RAND_WALK;
      }

      goto SLS_MOVE;
    }
  }
  else
  {
    slv->nslsmoves += 1;
  SLS_MOVE:
    select_candidates (btor, constr, &candidates);
    /* root is const false -> unsat */
    if (!BTOR_COUNT_STACK (candidates))
    {
      res = 0;
      goto DONE;
    }

    slv->max_score = compute_sls_score_formula (btor, slv->score, 0);
    slv->max_move  = BTOR_SLS_MOVE_DONE;
    slv->max_gw    = -1;

    if (btor_opt_get (btor, BTOR_OPT_SLS_MOVE_RAND_WALK)
        && btor_pick_with_prob_rng (
               &btor->rng,
               btor_opt_get (btor, BTOR_OPT_SLS_PROB_MOVE_RAND_WALK)))
    {
    SLS_MOVE_RAND_WALK:
      select_random_move (btor, &candidates);
    }
    else
    {
      select_move (btor, &candidates);
      if (slv->terminate) goto DONE;
    }

    assert (slv->max_cans->count);
  }
  assert (slv->max_move != BTOR_SLS_MOVE_DONE);

  if (nprops == slv->npropmoves && nsls == slv->nslsmoves)
  {
    slv->npropmoves = slv->nslsmoves = 0;
  }

#ifndef NBTORLOG
  BTORLOG (1, "");
  BTORLOG (1, " * move");
  char *a;
  BtorBitVector *ass;
  btor_init_int_hash_table_iterator (&iit, slv->max_cans);
  while (btor_has_next_int_hash_table_iterator (&iit))
  {
    neigh = (BtorBitVector *) slv->max_cans->data[iit.cur_pos].as_ptr;
    can = btor_get_node_by_id (btor, btor_next_int_hash_table_iterator (&iit));
    ass = (BtorBitVector *) btor_model_get_bv (btor, can);
    a   = btor_bv_to_char (btor->mm, ass);
    BTORLOG (1,
             "  candidate: %s%s",
             BTOR_IS_REGULAR_NODE (can) ? "" : "-",
             node2string (can));
    BTORLOG (1, "  prev. assignment: %s", a);
    btor_freestr (btor->mm, a);
    a = btor_bv_to_char (btor->mm, neigh);
    BTORLOG (1, "  new   assignment: %s", a);
    btor_freestr (btor->mm, a);
  }
#endif

  btor_propsls_update_cone (btor,
                            btor->bv_model,
                            slv->roots,
                            slv->score,
                            slv->max_cans,
                            true,
                            &slv->stats.updates,
                            &slv->time.update_cone,
                            &slv->time.update_cone_reset,
                            &slv->time.update_cone_model_gen,
                            &slv->time.update_cone_compute_score);

  slv->stats.moves += 1;

  assert (slv->max_move != BTOR_SLS_MOVE_DONE);
  assert (slv->max_gw >= 0);

  switch (slv->max_move)
  {
    case BTOR_SLS_MOVE_FLIP:
      if (!slv->max_gw)
        slv->stats.move_flip += 1;
      else
        slv->stats.move_gw_flip += 1;
      break;
    case BTOR_SLS_MOVE_INC:
      if (!slv->max_gw)
        slv->stats.move_inc += 1;
      else
        slv->stats.move_gw_inc += 1;
      break;
    case BTOR_SLS_MOVE_DEC:
      if (!slv->max_gw)
        slv->stats.move_dec += 1;
      else
        slv->stats.move_gw_dec += 1;
      break;
    case BTOR_SLS_MOVE_NOT:
      if (!slv->max_gw)
        slv->stats.move_not += 1;
      else
        slv->stats.move_gw_not += 1;
      break;
    case BTOR_SLS_MOVE_FLIP_RANGE:
      if (!slv->max_gw)
        slv->stats.move_range += 1;
      else
        slv->stats.move_gw_range += 1;
      break;
    case BTOR_SLS_MOVE_FLIP_SEGMENT:
      if (!slv->max_gw)
        slv->stats.move_seg += 1;
      else
        slv->stats.move_gw_seg += 1;
      break;
    case BTOR_SLS_MOVE_RAND:
      if (!slv->max_gw)
        slv->stats.move_rand += 1;
      else
        slv->stats.move_gw_rand += 1;
      break;
    case BTOR_SLS_MOVE_RAND_WALK:
      if (!slv->max_gw)
        slv->stats.move_rand_walk += 1;
      else
        slv->stats.move_gw_rand_walk += 1;
      break;
    default:
      assert (slv->max_move == BTOR_SLS_MOVE_PROP);
      slv->stats.move_prop += 1;
  }

  if (slv->max_move == BTOR_SLS_MOVE_RAND) update_assertion_weights (btor);

  /** cleanup **/
DONE:
  btor_init_int_hash_table_iterator (&iit, slv->max_cans);
  while (btor_has_next_int_hash_table_iterator (&iit))
  {
    assert (slv->max_cans->data[iit.cur_pos].as_ptr);
    btor_bv_free (btor->mm,
                  btor_next_data_int_hash_table_iterator (&iit)->as_ptr);
  }
  btor_delete_int_hash_map (slv->max_cans);
  slv->max_cans = 0;
  BTOR_RELEASE_STACK (candidates);
  return res;
}

/*------------------------------------------------------------------------*/

void
clone_data_as_sls_constr_data_ptr (BtorMemMgr *mm,
                                   const void *map,
                                   BtorHashTableData *data,
                                   BtorHashTableData *cloned_data)
{
  assert (data);
  assert (cloned_data);

  BtorSLSConstrData *d, *cd;

  (void) map;
  d = (BtorSLSConstrData *) data->as_ptr;
  BTOR_CNEW (mm, cd);
  memcpy (cd, d, sizeof (BtorSLSConstrData));
  cloned_data->as_ptr = cd;
}

static BtorSLSSolver *
clone_sls_solver (Btor *clone, BtorSLSSolver *slv, BtorNodeMap *exp_map)
{
  assert (clone);
  assert (slv);
  assert (slv->kind == BTOR_SLS_SOLVER_KIND);

  int i;
  BtorSLSSolver *res;
  BtorSLSMove *m, *cm;

  (void) exp_map;

  BTOR_NEW (clone->mm, res);
  memcpy (res, slv, sizeof (BtorSLSSolver));

  res->btor  = clone;
  res->roots = btor_clone_int_hash_map (clone->mm, slv->roots, 0, 0);
  res->score = btor_clone_int_hash_map (
      clone->mm, slv->score, btor_clone_data_as_dbl, 0);

  BTOR_INIT_STACK (clone->mm, res->moves);
  assert (BTOR_SIZE_STACK (slv->moves) || !BTOR_COUNT_STACK (slv->moves));
  if (BTOR_SIZE_STACK (slv->moves))
  {
    BTOR_NEWN (clone->mm, res->moves.start, BTOR_SIZE_STACK (slv->moves));
    res->moves.top = res->moves.start;
    res->moves.end = res->moves.start + BTOR_SIZE_STACK (slv->moves);

    for (i = 0; i < BTOR_COUNT_STACK (slv->moves); i++)
    {
      m = BTOR_PEEK_STACK (slv->moves, i);
      assert (m);
      BTOR_NEW (clone->mm, cm);
      cm->cans = btor_clone_int_hash_map (
          clone->mm, m->cans, btor_clone_data_as_bv_ptr, 0);
      cm->sc = m->sc;
      BTOR_PUSH_STACK (res->moves, m);
    }
  }
  assert (BTOR_COUNT_STACK (slv->moves) == BTOR_COUNT_STACK (res->moves));
  assert (BTOR_SIZE_STACK (slv->moves) == BTOR_SIZE_STACK (res->moves));

  res->max_cans = btor_clone_int_hash_map (
      clone->mm, slv->max_cans, btor_clone_data_as_bv_ptr, 0);

  return res;
}

static void
delete_sls_solver (BtorSLSSolver *slv)
{
  assert (slv);
  assert (slv->kind == BTOR_SLS_SOLVER_KIND);
  assert (slv->btor);
  assert (slv->btor->slv == (BtorSolver *) slv);

  Btor *btor;
  BtorIntHashTableIterator it;
  BtorSLSConstrData *d;
  BtorSLSMove *m;

  btor = slv->btor;

  if (slv->score) btor_delete_int_hash_map (slv->score);
  if (slv->roots) btor_delete_int_hash_map (slv->roots);
  if (slv->weights)
  {
    btor_init_int_hash_table_iterator (&it, slv->weights);
    while (btor_has_next_int_hash_table_iterator (&it))
    {
      d = btor_next_data_int_hash_table_iterator (&it)->as_ptr;
      BTOR_DELETE (btor->mm, d);
    }
    btor_delete_int_hash_map (slv->weights);
  }
  while (!BTOR_EMPTY_STACK (slv->moves))
  {
    m = BTOR_POP_STACK (slv->moves);
    btor_init_int_hash_table_iterator (&it, m->cans);
    while (btor_has_next_int_hash_table_iterator (&it))
      btor_bv_free (btor->mm,
                    btor_next_data_int_hash_table_iterator (&it)->as_ptr);
    btor_delete_int_hash_map (m->cans);
  }
  BTOR_RELEASE_STACK (slv->moves);
  if (slv->max_cans)
  {
    btor_init_int_hash_table_iterator (&it, slv->max_cans);
    while (btor_has_next_int_hash_table_iterator (&it))
    {
      assert (slv->max_cans->data[it.cur_pos].as_ptr);
      btor_bv_free (btor->mm,
                    btor_next_data_int_hash_table_iterator (&it)->as_ptr);
    }
    btor_delete_int_hash_map (slv->max_cans);
  }
  BTOR_DELETE (btor->mm, slv);
}

/* Note: failed assumptions -> no handling necessary, sls only works for SAT
 * Note: limits are currently unused */
static BtorSolverResult
sat_sls_solver (BtorSLSSolver *slv)
{
  assert (slv);
  assert (slv->kind == BTOR_SLS_SOLVER_KIND);
  assert (slv->btor);
  assert (slv->btor->slv == (BtorSolver *) slv);

  int32_t j, max_steps, id, nmoves;
  uint32_t nprops;
  BtorSolverResult sat_result;
  BtorNode *root;
  BtorSLSConstrData *d;
  BtorPtrHashTableIterator pit;
  BtorIntHashTableIterator iit;
  Btor *btor;

  btor = slv->btor;
  assert (!btor->inconsistent);
  nmoves      = 0;
  nprops      = btor_opt_get (btor, BTOR_OPT_PROP_NPROPS);
  slv->nflips = btor_opt_get (btor, BTOR_OPT_SLS_NFLIPS);

  if (btor_terminate_btor (btor))
  {
    sat_result = BTOR_RESULT_UNKNOWN;
    goto DONE;
  }

  BTOR_ABORT (btor->ufs->count != 0
                  || (!btor_opt_get (btor, BTOR_OPT_BETA_REDUCE_ALL)
                      && btor->lambdas->count != 0),
              "sls engine supports QF_BV only");

  /* Generate intial model, all bv vars are initialized with zero. We do
   * not have to consider model_for_all_nodes, but let this be handled by
   * the model generation (if enabled) after SAT has been determined. */
  slv->api.generate_model ((BtorSolver *) slv, false, true);

  /* init assertion weights of ALL roots */
  assert (!slv->weights);
  slv->weights = btor_new_int_hash_map (btor->mm);
  assert (btor->synthesized_constraints->count == 0);
  btor_init_ptr_hash_table_iterator (&pit, btor->unsynthesized_constraints);
  while (btor_has_next_ptr_hash_table_iterator (&pit))
  {
    root = btor_next_ptr_hash_table_iterator (&pit);
    assert (!btor_get_ptr_hash_table (btor->unsynthesized_constraints,
                                      BTOR_INVERT_NODE (root)));
    id = btor_exp_get_id (root);
    if (!btor_contains_int_hash_map (slv->weights, id))
    {
      BTOR_CNEW (btor->mm, d);
      d->weight = 1; /* initial assertion weight */
      btor_add_int_hash_map (slv->weights, id)->as_ptr = d;
    }
  }
  btor_init_ptr_hash_table_iterator (&pit, btor->assumptions);
  while (btor_has_next_ptr_hash_table_iterator (&pit))
  {
    root = btor_next_ptr_hash_table_iterator (&pit);
    if (btor_get_ptr_hash_table (btor->unsynthesized_constraints,
                                 BTOR_INVERT_NODE (root)))
      goto UNSAT;
    if (btor_get_ptr_hash_table (btor->assumptions, BTOR_INVERT_NODE (root)))
      goto UNSAT;
    id = btor_exp_get_id (root);
    if (!btor_contains_int_hash_map (slv->weights, id))
    {
      BTOR_CNEW (btor->mm, d);
      d->weight = 1; /* initial assertion weight */
      btor_add_int_hash_map (slv->weights, id)->as_ptr = d;
    }
  }

  if (!slv->score) slv->score = btor_new_int_hash_map (btor->mm);

  for (;;)
  {
    if (btor_terminate_btor (btor))
    {
      sat_result = BTOR_RESULT_UNKNOWN;
      goto DONE;
    }

    /* init */
    slv->prop_flip_cond_const_prob =
        btor_opt_get (btor, BTOR_OPT_PROP_PROB_FLIP_COND_CONST);
    slv->prop_flip_cond_const_prob_delta =
        slv->prop_flip_cond_const_prob > (BTOR_PROB_MAX / 2)
            ? -BTOR_PROPSLS_PROB_FLIP_COND_CONST_DELTA
            : BTOR_PROPSLS_PROB_FLIP_COND_CONST_DELTA;

    /* collect unsatisfied roots (kept up-to-date in update_cone) */
    assert (!slv->roots);
    slv->roots = btor_new_int_hash_map (btor->mm);
    assert (btor->synthesized_constraints->count == 0);
    btor_init_ptr_hash_table_iterator (&pit, btor->unsynthesized_constraints);
    btor_queue_ptr_hash_table_iterator (&pit, btor->assumptions);
    while (btor_has_next_ptr_hash_table_iterator (&pit))
    {
      root = btor_next_ptr_hash_table_iterator (&pit);
      if (!btor_contains_int_hash_map (slv->roots, btor_exp_get_id (root))
          && btor_bv_is_zero (btor_model_get_bv (btor, root)))
      {
        if (btor_is_bv_const_node (root))
          goto UNSAT; /* contains false constraint -> unsat */
        btor_add_int_hash_map (slv->roots, btor_exp_get_id (root));
      }
    }

    /* compute initial sls score */
    btor_propsls_compute_sls_scores (
        btor, btor->bv_model, btor->fun_model, slv->score);

    if (!slv->roots->count) goto SAT;

    for (j = 0, max_steps = BTOR_SLS_MAXSTEPS (slv->stats.restarts + 1);
         !btor_opt_get (btor, BTOR_OPT_SLS_USE_RESTARTS) || j < max_steps;
         j++)
    {
      if (btor_terminate_btor (btor)
          || (slv->nflips && slv->stats.flips >= slv->nflips)
          || (nprops && slv->stats.props >= nprops))
      {
        sat_result = BTOR_RESULT_UNKNOWN;
        goto DONE;
      }

      if (!move (btor, nmoves)) goto UNSAT;
      nmoves += 1;

      if (!slv->roots->count) goto SAT;
    }

    /* restart */
    slv->api.generate_model ((BtorSolver *) slv, false, true);
    btor_delete_int_hash_map (slv->score);
    btor_delete_int_hash_map (slv->roots);
    slv->roots = 0;
    slv->score = btor_new_int_hash_map (btor->mm);
    slv->stats.restarts += 1;
  }

SAT:
  sat_result = BTOR_RESULT_SAT;
  goto DONE;

UNSAT:
  sat_result = BTOR_RESULT_UNSAT;

DONE:
  if (slv->roots)
  {
    btor_delete_int_hash_map (slv->roots);
    slv->roots = 0;
  }
  if (slv->weights)
  {
    btor_init_int_hash_table_iterator (&iit, slv->weights);
    while (btor_has_next_int_hash_table_iterator (&iit))
      BTOR_DELETE (
          btor->mm,
          (BtorSLSConstrData *) btor_next_data_int_hash_table_iterator (&iit)
              ->as_ptr);
    btor_delete_int_hash_map (slv->weights);
    slv->weights = 0;
  }
  if (slv->score)
  {
    btor_delete_int_hash_map (slv->score);
    slv->score = 0;
  }
  return sat_result;
}

static void
generate_model_sls_solver (BtorSLSSolver *slv,
                           bool model_for_all_nodes,
                           bool reset)
{
  assert (slv);
  assert (slv->kind == BTOR_SLS_SOLVER_KIND);
  assert (slv->btor);
  assert (slv->btor->slv == (BtorSolver *) slv);

  Btor *btor;

  btor = slv->btor;

  if (!reset && btor->bv_model) return;
  btor_model_init_bv (btor, &btor->bv_model);
  btor_model_init_fun (btor, &btor->fun_model);
  btor_model_generate (
      btor, btor->bv_model, btor->fun_model, model_for_all_nodes);
}

static void
print_stats_sls_solver (BtorSLSSolver *slv)
{
  assert (slv);
  assert (slv->kind == BTOR_SLS_SOLVER_KIND);
  assert (slv->btor);
  assert (slv->btor->slv == (BtorSolver *) slv);

  Btor *btor;

  btor = slv->btor;

  BTOR_MSG (btor->msg, 1, "");
  BTOR_MSG (btor->msg, 1, "sls restarts: %d", slv->stats.restarts);
  BTOR_MSG (btor->msg, 1, "sls moves: %d", slv->stats.moves);
  BTOR_MSG (btor->msg, 1, "sls flips: %d", slv->stats.flips);
  BTOR_MSG (btor->msg, 1, "sls propagation steps: %u", slv->stats.props);
  BTOR_MSG (btor->msg, 1, "");
  BTOR_MSG (btor->msg,
            1,
            "sls propagation move conflicts (recoverable): %d",
            slv->stats.move_prop_rec_conf);
  BTOR_MSG (btor->msg,
            1,
            "sls propagation move conflicts (non-recoverable): %d",
            slv->stats.move_prop_non_rec_conf);

  BTOR_MSG (btor->msg, 1, "");
  BTOR_MSG (btor->msg, 1, "sls flip        moves: %d", slv->stats.move_flip);
  BTOR_MSG (btor->msg, 1, "sls inc         moves: %d", slv->stats.move_inc);
  BTOR_MSG (btor->msg, 1, "sls dec         moves: %d", slv->stats.move_dec);
  BTOR_MSG (btor->msg, 1, "sls not         moves: %d", slv->stats.move_not);
  BTOR_MSG (btor->msg, 1, "sls range       moves: %d", slv->stats.move_range);
  BTOR_MSG (btor->msg, 1, "sls segment     moves: %d", slv->stats.move_seg);
  BTOR_MSG (btor->msg, 1, "sls random      moves: %d", slv->stats.move_rand);
  BTOR_MSG (
      btor->msg, 1, "sls random walk moves: %d", slv->stats.move_rand_walk);
  BTOR_MSG (btor->msg, 1, "sls propagation moves: %d", slv->stats.move_prop);

  BTOR_MSG (btor->msg, 1, "");
  BTOR_MSG (
      btor->msg, 1, "sls gw flip        moves: %d", slv->stats.move_gw_flip);
  BTOR_MSG (
      btor->msg, 1, "sls gw inc         moves: %d", slv->stats.move_gw_inc);
  BTOR_MSG (
      btor->msg, 1, "sls gw dec         moves: %d", slv->stats.move_gw_dec);
  BTOR_MSG (
      btor->msg, 1, "sls gw not         moves: %d", slv->stats.move_gw_not);
  BTOR_MSG (
      btor->msg, 1, "sls gw range       moves: %d", slv->stats.move_gw_range);
  BTOR_MSG (
      btor->msg, 1, "sls gw segment     moves: %d", slv->stats.move_gw_seg);
  BTOR_MSG (
      btor->msg, 1, "sls gw random      moves: %d", slv->stats.move_gw_rand);
  BTOR_MSG (btor->msg,
            1,
            "sls gw random walk moves: %d",
            slv->stats.move_gw_rand_walk);
}

static void
print_time_stats_sls_solver (BtorSLSSolver *slv)
{
  assert (slv);
  assert (slv->kind == BTOR_SLS_SOLVER_KIND);
  assert (slv->btor);
  assert (slv->btor->slv == (BtorSolver *) slv);

  Btor *btor = slv->btor;

  BTOR_MSG (btor->msg, 1, "");
  BTOR_MSG (btor->msg,
            1,
            "%.2f seconds for updating cone (total)",
            slv->time.update_cone);
  BTOR_MSG (btor->msg,
            1,
            "%.2f seconds for updating cone (reset)",
            slv->time.update_cone_reset);
  BTOR_MSG (btor->msg,
            1,
            "%.2f seconds for updating cone (model gen)",
            slv->time.update_cone_model_gen);
  BTOR_MSG (btor->msg,
            1,
            "%.2f seconds for updating cone (compute score)",
            slv->time.update_cone_compute_score);
  BTOR_MSG (btor->msg, 1, "");
}

BtorSolver *
btor_new_sls_solver (Btor *btor)
{
  assert (btor);

  BtorSLSSolver *slv;

  BTOR_CNEW (btor->mm, slv);

  slv->kind = BTOR_SLS_SOLVER_KIND;
  slv->btor = btor;

  BTOR_INIT_STACK (btor->mm, slv->moves);

  slv->api.clone          = (BtorSolverClone) clone_sls_solver;
  slv->api.delet          = (BtorSolverDelete) delete_sls_solver;
  slv->api.sat            = (BtorSolverSat) sat_sls_solver;
  slv->api.generate_model = (BtorSolverGenerateModel) generate_model_sls_solver;
  slv->api.print_stats    = (BtorSolverPrintStats) print_stats_sls_solver;
  slv->api.print_time_stats =
      (BtorSolverPrintTimeStats) print_time_stats_sls_solver;

  BTOR_MSG (btor->msg, 1, "enabled sls engine");

  return (BtorSolver *) slv;
}

/*------------------------------------------------------------------------*/
