/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2014 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btoropt.h"
#include <ctype.h>
#include "boolector.h"
#include "btorcore.h"
#include "btoriter.h"
#include "btorlog.h"
#include "btormodel.h"
#include "btortrapi.h"

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
    uname[i] = toupper (lname[j]);
  }

  return getenv (uname);
}

static void
set_opt_values (BtorOpt *opt,
                int internal,
                char *shrt,
                char *lng,
                int val,
                int min,
                int max,
                char *desc)
{
  assert (opt);
  assert (min <= val);
  assert (max == -1 || val <= max);

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
  int val;
  char *valstr;

  BTOR_OPT ("m", model_gen, 0, 0, 2, "print model for satisfiable instances");

  BTOR_OPT ("i", incremental, 0, 0, 1, "incremental usage (SMT1 only)");
  BTOR_OPT ("I",
            incremental_all,
            0,
            0,
            1,
            "incremental usage, solve all (SMT1 only)");
  BTOR_OPT (0,
            incremental_in_depth,
            0,
            0,
            1,
            "incremental in-depth mode width (SMT1 only)");
  BTOR_OPT (0,
            incremental_look_ahead,
            0,
            0,
            1,
            "incremental look-ahead width (SMT1 only)");
  BTOR_OPT (0,
            incremental_interval,
            0,
            0,
            1,
            "incremental interval mode width (SMT1 only)");

  BTOR_OPT_INTL (0,
                 input_format,
                 0,
                 BTOR_INPUT_FORMAT_BTOR,
                 BTOR_INPUT_FORMAT_SMT2,
                 "input file format");
  BTOR_OPT_INTL (0,
                 output_number_format,
                 BTOR_OUTPUT_BASE_BIN,
                 BTOR_OUTPUT_BASE_BIN,
                 BTOR_OUTPUT_BASE_DEC,
                 "output number format");
  BTOR_OPT_INTL (0,
                 output_format,
                 BTOR_OUTPUT_FORMAT_BTOR,
                 BTOR_OUTPUT_FORMAT_BTOR,
                 BTOR_OUTPUT_FORMAT_SMT2,
                 "output file format");

  BTOR_OPT ("rwl", rewrite_level, 3, 0, 3, "rewrite level");
  BTOR_OPT (
      0, rewrite_level_pbr, 1, 0, 3, "rewrite level partial beta reduction");

  BTOR_OPT (
      "bra", beta_reduce_all, 0, 0, 1, "eagerly eliminate lambda expressions");
#ifdef BTOR_ENABLE_BETA_REDUCTION_PROBING
  BTOR_OPT ("pbra",
            probe_beta_reduce_all,
            0,
            0,
            1,
            "probe '-bra' until given LOD or SAT limit");
  BTOR_OPT (0, pbra_lod_limit, 10, 0, -1, "LOD limit (#lemmas) for -pbra");
  BTOR_OPT (
      0, pbra_sat_limit, 55000, 0, -1, "SAT limit (#conflicts) for -pbra");
  BTOR_OPT (0,
            pbra_ops_factor,
            10,
            0,
            -1,
            "factor by which the size of the red. formula may be greater than "
            "the original formula");
#endif

#ifdef BTOR_ENABLE_DUAL_PROPAGATION
  BTOR_OPT ("dp", dual_prop, 0, 0, 1, "dual propagation optimization");
#endif
  BTOR_OPT ("ju", just, 0, 0, 1, "justification optimization");
#ifndef BTOR_DO_NOT_OPTIMIZE_UNCONSTRAINED
  BTOR_OPT ("uc", ucopt, 0, 0, 1, "unconstrained optimization");
#endif
  BTOR_OPT ("ls", lazy_synthesize, 1, 0, 1, "lazily synthesize expressions");
  BTOR_OPT ("es", eliminate_slices, 1, 0, 1, "eliminate slices on variables");
  BTOR_OPT_INTL ("fc", force_cleanup, 0, 0, 1, "force cleanup on exit");
  BTOR_OPT ("p", pretty_print, 1, 0, 1, "pretty print when dumping");
#ifndef NBTORLOG
  BTOR_OPT ("l", loglevel, 0, 0, BTORLOG_LEVEL_MAX, "increase loglevel");
#endif
  BTOR_OPT ("v", verbosity, 0, 0, BTOR_VERBOSITY_MAX, "increase verbosity");

  BTOR_OPT_INTL (0, simplify_constraints, 1, 0, 1, 0);
  BTOR_OPT_INTL (0, force_internal_cleanup, 0, 0, 1, 0);
#ifdef BTOR_CHECK_FAILED
  BTOR_OPT_INTL (0, chk_failed_assumptions, 1, 0, 1, 0);
#endif
}

#define BTOR_FIRST_OPT(btor) (&(btor)->options.first + 1)
#define BTOR_LAST_OPT(btor) (&(btor)->options.last - 1)

BtorOpt *
btor_get_opt_aux (Btor *btor, const char *name)
{
  assert (btor);
  assert (name);

  BtorOpt *o;

  for (o = BTOR_FIRST_OPT (btor); o <= BTOR_LAST_OPT (btor); o++)
    if ((o->shrt && !strcmp (o->shrt, name))
        || (o->lng && !strcmp (o->lng, name)))
      return o;

  return 0;
}

BtorOpt *
btor_get_opt (Btor *btor, const char *name)
{
  BtorOpt *o = btor_get_opt_aux (btor, name);
  assert (o);
  return o;
}

int
btor_get_opt_val (Btor *btor, const char *name)
{
  return btor_get_opt (btor, name)->val;
}

void
btor_set_opt (Btor *btor, const char *name, int val)
{
  assert (btor);
  assert (name);

  BtorOpt *o;
  BtorAIGVecMgr *avmgr;
  BtorAIGMgr *amgr;
  BtorSATMgr *smgr;

  o = btor_get_opt (btor, name);
  assert (o);
#ifndef NDEBUG
  int oldval = o->val;
#endif
  if (val > o->max) val = o->max;
  if (val < o->min) val = o->min;
  o->val = val;

  if (!strcmp (name, "m") || !strcmp (name, BTOR_OPT_MODEL_GEN))
  {
    if (!val && btor->options.model_gen.val) btor_delete_model (btor);
  }
  else if (!strcmp (name, "i") || !strcmp (name, BTOR_OPT_INCREMENTAL))
  {
    assert (val > 0);
    assert (btor->btor_sat_btor_called == 0);
    // TODO reset incremental usage, meltall if inc is disabled
  }
#ifdef BTOR_ENABLE_DUAL_PROPAGATION
  else if (!strcmp (name, "dp") || !strcmp (name, BTOR_OPT_DUAL_PROP))
  {
    assert (!val || !btor->options.just.val);
  }
#endif
  else if (!strcmp (name, "ju") || !strcmp (name, BTOR_OPT_JUST))
  {
#ifdef BTOR_ENABLE_DUAL_PROPAGATION
    assert (!val || !btor->options.dual_prop.val);
#endif
  }
  else if (!strcmp (name, "v") || !strcmp (name, BTOR_OPT_VERBOSITY))
  {
    assert (oldval >= -1);

    avmgr = btor->avmgr;
    amgr  = btor_get_aig_mgr_aigvec_mgr (avmgr);
    smgr  = btor_get_sat_mgr_aig_mgr (amgr);
    btor_set_verbosity_aigvec_mgr (avmgr, val);
    btor_set_verbosity_aig_mgr (amgr, val);
    btor_set_verbosity_sat_mgr (smgr, val);
  }
  else if (!strcmp (name, "rwl") || !strcmp (name, BTOR_OPT_REWRITE_LEVEL))
  {
    assert (val >= 0 && val <= 3);
    assert (oldval >= 0 && oldval <= 3);
  }
  else if (!strcmp (name, BTOR_OPT_REWRITE_LEVEL_PBR))
  {
    assert (val >= 0 && val <= 3);
    assert (oldval >= 0 && oldval <= 3);
  }
#ifdef NBTORLOG
  else if (!strcmp (name, BTOR_OPT_LOGLEVEL))
    return;
#endif
}

BtorOpt *
btor_first_opt (Btor *btor)
{
  assert (btor);
  return BTOR_FIRST_OPT (btor);
}

BtorOpt *
btor_last_opt (Btor *btor)
{
  assert (btor);
  return BTOR_LAST_OPT (btor);
}

BtorOpt *
btor_next_opt (Btor *btor, const BtorOpt *cur)
{
  assert (btor);
  assert (cur);

  if (cur + 1 > BTOR_LAST_OPT (btor)) return 0;
  return ((BtorOpt *) cur) + 1;
}
