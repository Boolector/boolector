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
#include "btortrapi.h"

#define BTOR_SET_OPT_FLAG(lng, val)   \
  do                                  \
  {                                   \
    if (val)                          \
      boolector_enable_##lng (btor);  \
    else                              \
      boolector_disable_##lng (btor); \
  } while (0)

#define BTOR_SET_OPT_VAL(lng, val)   \
  do                                 \
  {                                  \
    boolector_set_##lng (btor, val); \
  } while (0)

static void
btor_getenv (Btor *btor, BtorOpt *opt, const char *lname)
{
  assert (btor);
  assert (opt);
  assert (lname);

  char uname[40];
  const char *valstr;
  size_t i, j;
  int oldval, newval;

  assert (strlen (lname) + 4 + 1 < sizeof (uname));
  uname[0] = 'B';
  uname[1] = 'T';
  uname[2] = 'O';
  uname[3] = 'R';
  for (i = 4, j = 0; i < sizeof (uname); i++, j++)
    uname[i] = toupper (lname[j]);
  uname[i] = '\0';

  valstr = getenv (uname);
  if (!valstr) return;

  oldval = opt->val;
  newval = atoi (valstr);
  if (newval < opt->min) newval = opt->min;
  if (newval > opt->max) newval = opt->max;
  if (newval == oldval) return;

  // TODO FIXME
  if (!strcmp (lname, "model_gen") && newval == 0) return;
  //

  opt->val = newval;
  if (opt->min == 0 && opt->max == 1)
    BTOR_TRAPI ("%s_%s", opt->val ? "enable" : "disable", lname);
  else
    BTOR_TRAPI ("set_%s %d", lname, opt->val);
}

// static void
// btor_set_opt_model_gen (Btor * btor, int val)
//{
//  assert (btor);
//  BTOR_SET_OPT_FLAG (model_gen, val);
//}
//
// static void
// btor_set_opt_generate_models_for_all_reads (Btor * btor, int val)
//{
//  assert (btor);
//  BTOR_SET_OPT_FLAG (generate_models_for_all_reads, val);
//}
//
// static void
// btor_set_opt_inc_enabled (Btor * btor, int val)
//{
//  assert (btor);
//  BTOR_SET_OPT_FLAG (inc_usage, val);
//}
//
// static void
// btor_set_opt_beta_reduce_all (Btor * btor, int val)
//{
//  assert (btor);
//  BTOR_SET_OPT_FLAG (beta_reduce_all, val);
//}
//
// static void
// btor_set_opt_dual_prop (Btor * btor, int val)
//{
//  assert (btor);
//  BTOR_SET_OPT_FLAG (dual_prop, val);
//}
//
// static void
// btor_set_opt_justification (Btor * btor, int val)
//{
//  assert (btor);
//  BTOR_SET_OPT_FLAG (justification, val);
//}
//
//#ifndef BTOR_DO_NOT_OPTIMIZE_UNCONSTRAINED
// static void
// btor_set_opt_ucopt (Btor * btor, int val)
//{
//  assert (btor);
//  BTOR_SET_OPT_FLAG (ucopt, val);
//}
//#endif
//
// static void
// btor_set_opt_force_cleanup (Btor * btor, int val)
//{
//  assert (btor);
//  BTOR_SET_OPT_FLAG (force_cleanup, val);
//}
//
// static void
// btor_set_opt_force_internal_cleanup (Btor * btor, int val)
//{
//  assert (btor);
//  BTOR_SET_OPT_FLAG (force_internal_cleanup, val);
//}
//
// static void
// btor_set_opt_rewrite_level (Btor * btor, int val)
//{
//  assert (btor);
//  BTOR_SET_OPT_VAL (rewrite_level, val);
//}
//
// static void
// btor_set_opt_rewrite_level_pbr (Btor * btor, int val)
//{
//  assert (btor);
//  BTOR_SET_OPT_VAL (rewrite_level_pbr, val);
//}
//
//#ifndef NBTOR_LOG
// static void
// btor_set_opt_loglevel (Btor * btor, int val)
//{
//  assert (btor);
//  BTOR_SET_OPT_VAL (loglevel, val);
//}
//#endif
//
// static void
// btor_set_opt_verbosity (Btor * btor, int val)
//{
//  assert (btor);
//  BTOR_SET_OPT_VAL (verbosity, val);
//}
