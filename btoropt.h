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

typedef struct Btor Btor;

typedef struct BtorOpt
{
  int internal;     /* internal option? */
  const char *shrt; /* short option identifier (may be 0) */
  const char *lng;  /* long option identifier */
  const char *desc; /* description */
  int val;          /* value */
  int dflt;         /* default value */
  int min;          /* min value */
  int max;          /* max value */
} BtorOpt;

typedef struct BtorOpts
{
  BtorOpt first; /* dummy for iteration */
  /* ----------------------------------------------------------------------- */
  BtorOpt model_gen;           /* model generation enabled */
  BtorOpt model_gen_all_reads; /* generate model for all reads */
  BtorOpt incremental;         /* incremental usage */

  BtorOpt rewrite_level;
  BtorOpt rewrite_level_pbr;

  BtorOpt beta_reduce_all; /* eagerly eliminate lambda expressions */
  BtorOpt dual_prop;       /* dual prop optimization */
  BtorOpt just;            /* justification optimization */
#ifndef BTOR_DO_NOT_OPTIMIZE_UNCONSTRAINED
  BtorOpt ucopt; /* unconstrained optimization */
#endif

  BtorOpt force_cleanup; /* force cleanup of exps, assignm. strings */
  BtorOpt pretty_print;  /* reindex exps when dumping */
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
  /* ----------------------------------------------------------------------- */
  BtorOpt last; /* dummy for iteration */

} BtorOpts;

void btor_init_opts (Btor *btor);

BtorOpt *btor_get_opt (Btor *btor, const char *opt);
void btor_set_opt (Btor *btor, const char *opt, int val);

BtorOpt *btor_first_opt (Btor *btor);
BtorOpt *btor_last_opt (Btor *btor);
BtorOpt *btor_next_opt (Btor *btor, BtorOpt *cur);

#endif
