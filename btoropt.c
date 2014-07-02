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
#include "btorlog.h"
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
  assert (val <= max);

  opt->internal = internal;
  opt->shrt     = shrt;
  opt->lng      = lng;
  opt->val      = val;
  opt->min      = min;
  opt->max      = max;
  opt->desc     = desc;
}

#define BTOR_SET_OPT(LNG, VAL)             \
  do                                       \
  {                                        \
    boolector_set_opt_##LNG (btor, VAL);   \
    printf ("set_opt_%s %d\n", #LNG, VAL); \
  } while (0)

#define BTOR_SET_OPT_INTL(LNG, VAL) \
  do                                \
  {                                 \
    btor_set_opt_##LNG (btor, VAL); \
  } while (0)

#define BTOR_OPT(SHRT, LNG, VAL, MIN, MAX, DESC)                             \
  do                                                                         \
  {                                                                          \
    set_opt_values (&btor->options.LNG, 0, SHRT, #LNG, VAL, MIN, MAX, DESC); \
    valstr = getenv_value (#LNG);                                            \
    if (valstr == NULL) break;                                               \
    val = atoi (valstr);                                                     \
    if (val < opt->min) val = opt->min;                                      \
    if (val > opt->max) val = opt->max;                                      \
    if (val == opt->val) break;                                              \
    BTOR_SET_OPT (LNG, val);                                                 \
  } while (0)

#define BTOR_OPT_INTL(SHRT, LNG, VAL, MIN, MAX, DESC)                        \
  do                                                                         \
  {                                                                          \
    set_opt_values (&btor->options.LNG, 1, SHRT, #LNG, VAL, MIN, MAX, DESC); \
    valstr = getenv_value (#LNG);                                            \
    if (valstr == NULL) break;                                               \
    val = atoi (valstr);                                                     \
    if (val < opt->min) val = opt->min;                                      \
    if (val > opt->max) val = opt->max;                                      \
    if (val == opt->val) break;                                              \
    BTOR_SET_OPT_INTL (LNG, val);                                            \
  } while (0)

void
btor_init_opts (Btor *btor)
{
  BtorOpt *opt = 0;
  int val;
  char *valstr;

  BTOR_OPT ("m", model_gen, 0, 0, 1, "print model for satisfiable instances");
  BTOR_OPT (0, model_gen_all_reads, 0, 0, 1, "generate model for all reads");
  BTOR_OPT ("i", incremental, 0, 0, 1, "incremental usage (SMT1 only)");
  BTOR_OPT (
      "bra", beta_reduce_all, 0, 0, 1, "eagerly eliminate lambda expressions");
  BTOR_OPT ("dp", dual_prop, 0, 0, 1, "enable dual propagation optimization");
  BTOR_OPT ("ju", just, 0, 0, 1, "enable justification optimization");
  BTOR_OPT ("uc", ucopt, 0, 0, 1, "enable unconstrained optimization");
  BTOR_OPT ("fc", force_cleanup, 0, 0, 1, "force cleanup on exit");
  BTOR_OPT ("p", pretty_print, 1, 0, 1, "pretty print when dumping");

  BTOR_OPT ("rwl", rewrite_level, 3, 0, 3, "set rewrite level");
  BTOR_OPT (0,
            rewrite_level_pbr,
            1,
            0,
            3,
            "set rewrite level for partial beta reduction");
#ifndef NBTORLOG
  BTOR_OPT ("l", loglevel, 0, 0, BTORLOG_LEVEL_MAX, "increase loglevel");
#endif
  BTOR_OPT ("v", verbosity, 0, 0, BTOR_VERBOSITY_MAX, "increase verbosity");

  BTOR_OPT_INTL (0, simplify_constraints, 1, 0, 1, 0);
  BTOR_OPT_INTL (0, propagate_slices, 0, 0, 1, 0);
  BTOR_OPT_INTL (0, force_internal_cleanup, 0, 0, 1, 0);
#ifdef BTOR_CHECK_FAILED
  BTOR_OPT_INTL (0, chk_failed_assumptions, 1, 0, 1, 0);
#endif
}
