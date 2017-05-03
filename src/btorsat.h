/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2014 Armin Biere.
 *  Copyright (C) 2013-2017 Aina Niemetz.
 *  Copyright (C) 2012-2016 Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORSAT_H_INCLUDED
#define BTORSAT_H_INCLUDED

#include "btortypes.h"
#include "utils/btormem.h"

#include <stdbool.h>
#include <stdio.h>

/*------------------------------------------------------------------------*/

typedef struct BtorSATMgr BtorSATMgr;

struct BtorSATMgr
{
  /* Note: direct solver reference for PicoSAT, wrapper object for for
   *	   Lingeling (BtorLGL) and MiniSAT (BtorMiniSAT). */
  void *solver;
  Btor *btor;

  const char *name; /* solver name */

  /* Note: do not change order! (btor_sat_mgr_clone relies on inc_required
   * to come first of all fields following below.) */
  bool inc_required;
#ifdef BTOR_USE_LINGELING
  bool fork;
#endif
  FILE *output;

  bool initialized;
  int satcalls;
  int clauses;
  int32_t true_lit;
  int maxvar;

  double sat_time;

  struct
  {
    int (*fun) (void *); /* termination callback */
    void *state;
  } term;

  struct
  {
    void (*add) (BtorSATMgr *, int); /* required */
    void (*assume) (BtorSATMgr *, int);
    int (*deref) (BtorSATMgr *, int); /* required */
    void (*enable_verbosity) (BtorSATMgr *, int);
    int (*failed) (BtorSATMgr *, int);
    int (*fixed) (BtorSATMgr *, int);
    int (*inc_max_var) (BtorSATMgr *);
    void *(*init) (BtorSATMgr *); /* required */
    void (*melt) (BtorSATMgr *, int);
    int (*repr) (BtorSATMgr *, int);
    void (*reset) (BtorSATMgr *);   /* required */
    int (*sat) (BtorSATMgr *, int); /* required */
    void (*set_output) (BtorSATMgr *, FILE *);
    void (*set_prefix) (BtorSATMgr *, const char *);
    void (*stats) (BtorSATMgr *);
    void *(*clone) (BtorSATMgr *, BtorMemMgr *);
    void (*setterm) (BtorSATMgr *);
  } api;
};

/*------------------------------------------------------------------------*/

/* Creates new SAT manager.
 * A SAT manager is used by nearly all functions of the SAT layer.
 */
BtorSATMgr *btor_sat_mgr_new (Btor *btor);

bool btor_sat_mgr_has_clone_support (const BtorSATMgr *smgr);

bool btor_sat_mgr_has_term_support (const BtorSATMgr *smgr);

void btor_sat_mgr_set_term (BtorSATMgr *smgr, int (*fun) (void *), void *state);

/* Clones existing SAT manager (and underlying SAT solver). */
BtorSATMgr *btor_sat_mgr_clone (Btor *btor, BtorSATMgr *smgr);

/* Deletes SAT manager from memory. */
void btor_sat_mgr_delete (BtorSATMgr *smgr);

/* Generates fresh CNF indices.
 * Indices are generated in consecutive order. */
int btor_sat_mgr_next_cnf_id (BtorSATMgr *smgr);

/* Mark old CNF index as not used anymore. */
void btor_sat_mgr_release_cnf_id (BtorSATMgr *smgr, int);

#if 0
/* Returns the last CNF index that has been generated. */
int btor_get_last_cnf_id_sat_mgr (BtorSATMgr * smgr);
#endif

void btor_sat_enable_solver (BtorSATMgr *smgr);

/* Inits the SAT solver. */
void btor_sat_init (BtorSATMgr *smgr);

/* Returns if the SAT solver has already been initialized */
bool btor_sat_is_initialized (BtorSATMgr *smgr);

/* Sets the output file of the SAT solver. */
void btor_sat_set_output (BtorSATMgr *smgr, FILE *output);

/* Prints statistics of SAT solver. */
void btor_sat_print_stats (BtorSATMgr *smgr);

/* Adds literal to the current clause of the SAT solver.
 * 0 terminates the current clause.
 */
void btor_sat_add (BtorSATMgr *smgr, int lit);

/* Adds assumption to SAT solver.
 * Requires that SAT solver supports this.
 */
void btor_sat_assume (BtorSATMgr *smgr, int lit);

/* Checks whether an assumption failed during
 * the last SAT solver call 'btor_sat_check_sat'.
 */
int btor_sat_failed (BtorSATMgr *smgr, int lit);

/* Solves the SAT instance.
 * limit < 0 -> no limit.
 */
BtorSolverResult btor_sat_check_sat (BtorSATMgr *smgr, int limit);

/* Gets assignment of a literal (in the SAT case).
 * Do not call before calling btor_sat_check_sat.
 */
int btor_sat_deref (BtorSATMgr *smgr, int lit);

/* Gets equivalence class represenative of a literal
 * or the literal itself if it is in a singleton
 * equivalence, fixed or eliminated.
 * Do not call before calling btor_sat_check_sat.
 */
int btor_sat_repr (BtorSATMgr *smgr, int lit);

/* Gets assignment of a literal (in the SAT case)
 * similar to 'deref', but only consider top level.
 * Do not call before calling btor_sat_check_sat.
 */
int btor_sat_fixed (BtorSATMgr *smgr, int lit);

/* Resets the status of the SAT solver. */
void btor_sat_reset (BtorSATMgr *smgr);

#endif
