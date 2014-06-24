/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2014 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTOROPTS_H_INCLUDED
#define BTOROPTS_H_INCLUDED

typedef struct BtorOpt
{
  char shrt;
  const char *lng, *desc;
  int dflt, val, min, max;
} BtorOpt;

#define BTOR_OPT(shrt, lng, val, min, max, desc) \
  do                                             \
  {                                              \
    assert (min <= val);                         \
    assert (val <= max);                         \
    BtorOpt *opt = &btor->opts->lng;             \
    opt->shrt    = shrt;                         \
    opt->lng     = #lng;                         \
    opt->dflt = opt->val = val;                  \
    opt->min             = min;                  \
    opt->max             = max;                  \
    opt->desc            = desc;                 \
    btor_getenv (btor, opt, #lng);               \
  } while (0)

typedef struct BtorOpts
{
  BtorOpt model_gen; /* model generation enabled */
  BtorOpt generate_model_for_all_reads;
  BtorOpt inc_enabled; /* incremental usage */

  BtorOpt rewrite_level;
  BtorOpt rewrite_level_pbr;

  BtorOpt beta_reduce_all; /* eagerly eliminate lambda expressions */
  BtorOpt dual_prop;       /* dual prop optimization */
  BtorOpt just;            /* justification optimization */
#ifndef BTOR_DO_NOT_OPTIMIZE_UNCONSTRAINED
  BtorOpt ucopt; /* unconstrained optimization */
#endif

  BtorOpt force_cleanup; /* force cleanup of exps, assignm. strings */
  BtorOpt pprint;        /* reindex exps when dumping */
#ifndef NBTORLOG
  BtorOpt loglevel;
#endif
  BtorOpt verbosity;

  /* internal */
  BtorOpt simplify_constraints; /* force constraints to true/false */
  BtorOpt propagate_slices;
  BtorOpt force_internal_cleanup; /* force cleanup of exps, assignm. strings
                                     (internal references only) */
#ifdef BTOR_CHECK_FAILED
  BtorOpt chk_failed_assumptions;
#endif

} BtorOpts;

#endif
