/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2014-2015 Aina Niemetz.
 *  Copyright (C) 2014-2015 Mathias Preiner.
 *  Copyright (C) 2015 Armin Biere.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btoropt.h"
#include <ctype.h>
#include <limits.h>
#include "boolector.h"
#include "btorcore.h"
#include "btorlog.h"
#include "btormodel.h"
#include "btortrapi.h"
#include "utils/btoriter.h"

static char *
getenv_value (const char *lname)
{
  char uname[40];
  size_t i, j;

  assert (strlen (lname) + 4 + 1 < sizeof (uname));
  uname[0] = 'B';
  uname[1] = 'T';
  uname[2] = 'O';
  uname[3] = 'R';
  for (i = 4, j = 0; i < sizeof (uname); i++, j++)
  {
    if (lname[j] == '_')
    {
      i -= 1;
      continue;
    }
    uname[i] = toupper ((int) lname[j]);
  }

  return getenv (uname);
}

static void
set_opt_values (BtorOpt *opt,
                int internal,
                char *shrt,
                char *lng,
                uint32_t val,
                uint32_t min,
                uint32_t max,
                char *desc)
{
  assert (opt);
  assert (max <= UINT_MAX);
  assert (min <= val);
  assert (val <= max);

  opt->internal = internal;
  opt->shrt     = shrt;
  opt->lng      = lng;
  opt->val      = val;
  opt->dflt     = val;
  opt->min      = min;
  opt->max      = max;
  opt->desc     = desc;
}

#define BTOR_SET_OPT(LNG, VAL)           \
  do                                     \
  {                                      \
    boolector_set_opt (btor, #LNG, VAL); \
  } while (0)

#define BTOR_SET_OPT_INTL(LNG, VAL) \
  do                                \
  {                                 \
    btor_set_opt (btor, #LNG, VAL); \
  } while (0)

#define BTOR_OPT(SHRT, LNG, VAL, MIN, MAX, DESC)                             \
  do                                                                         \
  {                                                                          \
    set_opt_values (&btor->options.LNG, 0, SHRT, #LNG, VAL, MIN, MAX, DESC); \
    valstr = getenv_value (#LNG);                                            \
    if (valstr == NULL) break;                                               \
    val = atoi (valstr);                                                     \
    if (val < btor->options.LNG.min) val = btor->options.LNG.min;            \
    if (val > btor->options.LNG.max) val = btor->options.LNG.max;            \
    if (val == btor->options.LNG.val) break;                                 \
    BTOR_SET_OPT (LNG, val);                                                 \
  } while (0)

#define BTOR_OPT_INTL(SHRT, LNG, VAL, MIN, MAX, DESC)                        \
  do                                                                         \
  {                                                                          \
    set_opt_values (&btor->options.LNG, 1, SHRT, #LNG, VAL, MIN, MAX, DESC); \
    valstr = getenv_value (#LNG);                                            \
    if (valstr == NULL) break;                                               \
    val = atoi (valstr);                                                     \
    if (val < btor->options.LNG.min) val = btor->options.LNG.min;            \
    if (val > btor->options.LNG.max) val = btor->options.LNG.max;            \
    if (val == btor->options.LNG.val) break;                                 \
    BTOR_SET_OPT_INTL (LNG, val);                                            \
  } while (0)

void
btor_init_opts (Btor *btor)
{
  uint32_t val;
  char *valstr;

  BTOR_OPT ("m", model_gen, 0, 0, 2, "print model for satisfiable instances");

  BTOR_OPT ("i", incremental, 0, 0, 1, "incremental usage");
  BTOR_OPT (
      "I", incremental_all, 0, 0, 1, "incremental, solve all (SMT1 only)");

  BTOR_OPT (0,
            input_format,
            BTOR_INPUT_FORMAT_DFLT,
            BTOR_INPUT_FORMAT_MIN,
            BTOR_INPUT_FORMAT_MAX,
            "input file format");
  BTOR_OPT (0,
            output_number_format,
            BTOR_OUTPUT_BASE_DFLT,
            BTOR_OUTPUT_BASE_MIN,
            BTOR_OUTPUT_BASE_MAX,
            "output number format");
  BTOR_OPT (0,
            output_format,
            BTOR_OUTPUT_FORMAT_DFLT,
            BTOR_OUTPUT_FORMAT_MIN,
            BTOR_OUTPUT_FORMAT_MAX,
            "output file format");

  BTOR_OPT ("rwl", rewrite_level, 3, 0, 3, "rewrite level");

  BTOR_OPT (
      "bra", beta_reduce_all, 0, 0, 1, "eagerly eliminate lambda expressions");
  BTOR_OPT ("ack", ackermannize, 0, 0, 1, "add ackermann constraints");

  BTOR_OPT ("E",
            engine,
            BTOR_ENGINE_DFLT,
            BTOR_ENGINE_MIN,
            BTOR_ENGINE_MAX,
            "enable specific engine");
  BTOR_OPT ("SE",
            sat_engine,
            BTOR_SAT_ENGINE_DFLT,
            BTOR_SAT_ENGINE_MIN + 1,
            BTOR_SAT_ENGINE_MAX - 1,
            "enable specific SAT solver");

  // TODO MAKE SLS FACTORS CONFIGURABLE VIA BTOROPT
  BTOR_OPT (0,
            sls_strategy,
            BTOR_SLS_STRAT_DFLT,
            BTOR_SLS_STRAT_MIN,
            BTOR_SLS_STRAT_MAX,
            "move strategy for sls");
  BTOR_OPT (0,
            sls_move_gw,
            0,
            0,
            1,
            "select move by altering not only one but all candidate variables "
            "at once");
  BTOR_OPT (
      0, sls_move_range, 0, 0, 1, "try range-wise flips when selecting moves");
  BTOR_OPT (0,
            sls_move_segment,
            0,
            0,
            1,
            "try segment-wise flips when selecting moves");
  BTOR_OPT (0,
            sls_move_rand_walk,
            0,
            0,
            1,
            "do a random walk (with given probability)");
  BTOR_OPT (0,
            sls_move_rand_walk_prob,
            10,
            0,
            INT_MAX,
            "probability for choosing random walks (interpreted as 1:<n>)");
  BTOR_OPT (0,
            sls_move_rand_all,
            0,
            0,
            1,
            "randomize all candidate variables (instead of only one) if no "
            "neighbor with better score is found");
  BTOR_OPT (0,
            sls_move_rand_range,
            0,
            0,
            1,
            "randomize a range of bits of a randomly chosen candidate variable "
            "if neighbor with better score is found");
  BTOR_OPT (0,
            sls_move_prop,
            0,
            0,
            1,
            "enable propagation moves (with given ratio of propagation to "
            " regular moves)");
  BTOR_OPT (
      0,
      sls_move_prop_n_prop,
      1,
      0,
      UINT_MAX,
      "number of prop moves (moves are performed as <n>:m prop to sls moves");
  BTOR_OPT (
      0,
      sls_move_prop_n_sls,
      1,
      0,
      UINT_MAX,
      "number of sls moves (moves are performed as m:<n> prop to sls moves");
  BTOR_OPT (
      0,
      sls_move_prop_no_flip_cond,
      0,
      0,
      1,
      "do not choose to flip the condition for ITE during path selection");
  BTOR_OPT (0,
            sls_move_prop_force_rw,
            0,
            0,
            1,
            "force random walk if propagation move fails");
  BTOR_OPT (0,
            sls_move_prop_flip_cond_prob,
            10,
            0,
            INT_MAX,
            "probability for choosing to flip the condition (rather than "
            "choosing the enabled path) for ITE during path selection "
            "for prop moves (interpreted as 1:<n>)");
  BTOR_OPT (0,
            sls_move_inc_move_test,
            0,
            0,
            1,
            "use prev. neighbor with better score as base for next move test");

  BTOR_OPT (0, sls_use_restarts, 1, 0, 1, "use restarts");
  BTOR_OPT (
      0, sls_use_bandit, 1, 0, 1, "use bandit scheme for constraint selection");

  BTOR_OPT ("dp", dual_prop, 0, 0, 1, "dual propagation optimization");
  BTOR_OPT ("ju", just, 0, 0, 1, "justification optimization");
  BTOR_OPT (0,
            just_heuristic,
            BTOR_JUST_HEUR_DFLT,
            BTOR_JUST_HEUR_MIN,
            BTOR_JUST_HEUR_MAX,
            "justification heuristic");
#ifndef BTOR_DO_NOT_OPTIMIZE_UNCONSTRAINED
  BTOR_OPT ("uc", ucopt, 0, 0, 1, "unconstrained optimization");
#endif
  BTOR_OPT ("ls", lazy_synthesize, 0, 0, 1, "lazily synthesize expressions");
  BTOR_OPT ("es", eliminate_slices, 1, 0, 1, "eliminate slices on variables");
  BTOR_OPT ("el", eager_lemmas, 1, 0, 1, "eager lemma generation");
  BTOR_OPT ("ml", merge_lambdas, 1, 0, 1, "merge lambda chains");
  BTOR_OPT ("xl", extract_lambdas, 1, 0, 1, "extract lambda terms");
  BTOR_OPT (
      "sp", skeleton_preproc, 1, 0, 1, "propositional skeleton preprocessing");
  BTOR_OPT ("vs", var_subst, 1, 0, 1, "variable substitution");
  BTOR_OPT ("ms", miniscoping, 1, 0, 1, "miniscoping");
  BTOR_OPT (0, sort_exp, 1, 0, 1, "sort commutative expression nodes");
  BTOR_OPT (0, sort_aig, 1, 0, 1, "sort AIG nodes");
  BTOR_OPT (0, sort_aigvec, 1, 0, 1, "sort AIG vectors");
  BTOR_OPT ("ac", auto_cleanup, 0, 0, 1, "auto cleanup on exit");
  BTOR_OPT ("p", pretty_print, 1, 0, 1, "pretty print when dumping");
  BTOR_OPT ("e", exit_codes, 1, 0, 1, "use Boolector exit codes");
#ifndef NBTORLOG
  BTOR_OPT ("l", loglevel, 0, 0, UINT_MAX, "increase loglevel");
#endif
  BTOR_OPT ("v", verbosity, 0, 0, BTOR_VERBOSITY_MAX, "increase verbosity");
  BTOR_OPT ("s", seed, 0, 0, INT_MAX, "random number generator seed");

  BTOR_OPT_INTL (0, simplify_constraints, 1, 0, 1, 0);
  BTOR_OPT_INTL (0, auto_cleanup_internal, 0, 0, 1, 0);
#ifdef BTOR_CHECK_FAILED
  BTOR_OPT_INTL (0, chk_failed_assumptions, 1, 0, 1, 0);
#endif
  BTOR_OPT_INTL (0,
                 incremental_in_depth,
                 0,
                 0,
                 1,
                 "incremental in-depth mode width (SMT1 only)");
  BTOR_OPT_INTL (0,
                 incremental_look_ahead,
                 0,
                 0,
                 1,
                 "incremental look-ahead width (SMT1 only)");
  BTOR_OPT_INTL (0,
                 incremental_interval,
                 0,
                 0,
                 1,
                 "incremental interval mode width (SMT1 only)");
  BTOR_OPT_INTL (0, parse_interactive, 1, 0, 1, "interactive parse mode");
  BTOR_OPT_INTL (0, rw_normalize, 1, 0, 1, "normalize during rewriting");
#ifdef BTOR_USE_LINGELING
  BTOR_OPT_INTL (0, sat_engine_lgl_fork, 1, 0, 1, "fork lingeling");
#endif
}

#define BTOR_FIRST_OPT(btor) (&(btor)->options.first + 1)
#define BTOR_LAST_OPT(btor) (&(btor)->options.last - 1)

BtorOpt *
btor_get_opt_aux (Btor *btor, const char *name, int skip_internal)
{
  assert (btor);
  assert (name);

  BtorOpt *o;

  for (o = BTOR_FIRST_OPT (btor); o <= BTOR_LAST_OPT (btor); o++)
    if ((o->shrt && !strcmp (o->shrt, name))
        || (o->lng && !strcmp (o->lng, name)))
    {
      if (skip_internal && o->internal) continue;
      return o;
    }

  return 0;
}

BtorOpt *
btor_get_opt (Btor *btor, const char *name)
{
  BtorOpt *o = btor_get_opt_aux (btor, name, 0);
  return o;
}

int
btor_get_opt_val (Btor *btor, const char *name)
{
  return btor_get_opt (btor, name)->val;
}

int
btor_get_opt_min (Btor *btor, const char *name)
{
  return btor_get_opt (btor, name)->min;
}

int
btor_get_opt_max (Btor *btor, const char *name)
{
  return btor_get_opt (btor, name)->max;
}

int
btor_get_opt_dflt (Btor *btor, const char *name)
{
  return btor_get_opt (btor, name)->dflt;
}

const char *
btor_get_opt_shrt (Btor *btor, const char *name)
{
  return (const char *) btor_get_opt (btor, name)->shrt;
}

const char *
btor_get_opt_desc (Btor *btor, const char *name)
{
  return (const char *) btor_get_opt (btor, name)->desc;
}

void
btor_set_opt (Btor *btor, const char *name, uint32_t val)
{
  assert (btor);
  assert (name);

  BtorOpt *o;

#ifdef NBTORLOG
  if (!strcmp (name, BTOR_OPT_LOGLEVEL)) return;
#endif

  o = btor_get_opt (btor, name);
  assert (o);
#ifndef NDEBUG
  uint32_t oldval = o->val;
#endif
  if (val > o->max) val = o->max;
  if (val < o->min) val = o->min;
  o->val = val;

  if (!strcmp (name, "m") || !strcmp (name, BTOR_OPT_MODEL_GEN))
  {
    if (!val && btor->options.model_gen.val) btor_delete_model (btor);
    assert (!val || !btor->options.ucopt.val);
  }
  else if (!strcmp (name, "i") || !strcmp (name, BTOR_OPT_INCREMENTAL))
  {
    assert (val > 0);
    assert (btor->btor_sat_btor_called == 0);
  }
  else if (!strcmp (name, BTOR_OPT_INCREMENTAL_IN_DEPTH))
  {
    assert (val > 1);
    assert (!btor->options.incremental_look_ahead.val
            && !btor->options.incremental_interval.val);
  }
  else if (!strcmp (name, BTOR_OPT_INCREMENTAL_LOOK_AHEAD))
  {
    assert (val > 1);
    assert (!btor->options.incremental_in_depth.val
            && !btor->options.incremental_interval.val);
  }
  else if (!strcmp (name, BTOR_OPT_INCREMENTAL_INTERVAL))
  {
    assert (val > 1);
    assert (!btor->options.incremental_in_depth.val
            && !btor->options.incremental_look_ahead.val);
  }
  else if (!strcmp (name, "dp") || !strcmp (name, BTOR_OPT_DUAL_PROP))
  {
    assert (!val || !btor->options.just.val);
  }
  else if (!strcmp (name, "ju") || !strcmp (name, BTOR_OPT_JUST))
  {
    assert (!val || !btor->options.dual_prop.val);
  }
  else if (!strcmp (name, "sls") || !strcmp (name, BTOR_OPT_SLS))
  {
    assert (btor->btor_sat_btor_called == 0);
  }
  else if (!strcmp (name, "rwl") || !strcmp (name, BTOR_OPT_REWRITE_LEVEL))
  {
    assert (val <= 3);
    assert (oldval <= 3);
  }
}

void
btor_set_opt_str (Btor *btor, const char *name, const char *val)
{
  assert (btor);
  assert (name);
  assert (!strcmp (name, "se") || !strcmp (name, BTOR_OPT_SAT_ENGINE));

  BtorOpt *o;

  o = btor_get_opt (btor, name);
  assert (o);
  o->valstr = btor_strdup (btor->mm, val);
}

const char *
btor_first_opt (Btor *btor)
{
  assert (btor);
  assert (BTOR_FIRST_OPT (btor));
  return (const char *) BTOR_FIRST_OPT (btor)->lng;
}

const char *
btor_next_opt (Btor *btor, const char *cur)
{
  assert (btor);
  assert (cur);

  BtorOpt *cur_opt;

  cur_opt = btor_get_opt (btor, cur) + 1;
  /* skip internal options */
  while (cur_opt <= BTOR_LAST_OPT (btor) && cur_opt->internal) cur_opt += 1;
  if (cur_opt > BTOR_LAST_OPT (btor)) return 0;
  return (const char *) cur_opt->lng;
}
