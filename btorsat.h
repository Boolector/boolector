/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2014 Armin Biere.
 *  Copyright (C) 2013-2015 Aina Niemetz.
 *  Copyright (C) 2012-2015 Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORSAT_H_INCLUDED
#define BTORSAT_H_INCLUDED

#include "btormsg.h"
#include "btortypes.h"
#include "utils/btormem.h"

#include <stdio.h>

/*------------------------------------------------------------------------*/

typedef struct BtorSATMgr BtorSATMgr;

struct BtorSATMgr
{
  /* Note: direct solver reference for PicoSAT, wrapper object for for
   *	   Lingeling (BtorLGL) and MiniSAT (BtorMiniSAT). */
  void *solver;

  BtorMemMgr *mm;
  BtorMsg *msg;
  const char *name; /* solver name */
  char *optstr;     /* solver option string */

  /* Note: do not change order! (btor_clone_sat_mgr relies on inc_required
   * to come first of all fields following below.) */
  int inc_required;
#ifdef BTOR_USE_LINGELING
  bool fork;
#endif
  FILE *output;

  int satcalls;
  int initialized;
  int clauses;
  int true_lit;
  int maxvar;

  double sat_time;

  struct
  {
    int (*fun) (void *); /* termination callback */
    void *state;
  } term;

  struct
  {
    void (*add) (BtorSATMgr *, int);
    void (*assume) (BtorSATMgr *, int);
    int (*changed) (BtorSATMgr *);
    int (*deref) (BtorSATMgr *, int);
    void (*enable_verbosity) (BtorSATMgr *, int);
    int (*failed) (BtorSATMgr *, int);
    int (*fixed) (BtorSATMgr *, int);
    int (*inc_max_var) (BtorSATMgr *);
    int (*inconsistent) (BtorSATMgr *);
    void *(*init) (BtorSATMgr *);
    void (*melt) (BtorSATMgr *, int);
    int (*repr) (BtorSATMgr *, int);
    void (*reset) (BtorSATMgr *);
    int (*sat) (BtorSATMgr *, int);
    void (*set_output) (BtorSATMgr *, FILE *);
    void (*set_prefix) (BtorSATMgr *, const char *);
    void (*stats) (BtorSATMgr *);
    int (*variables) (BtorSATMgr *);
    void *(*clone) (BtorSATMgr *, BtorMemMgr *);
    void (*setterm) (BtorSATMgr *);
  } api;
};

#if defined(BTOR_USE_LINGELING)
#include "../lingeling/lglib.h"
typedef struct BtorLGL BtorLGL;

struct BtorLGL
{
  LGL *lgl;
  int nforked, blimit;
};
#endif

/*------------------------------------------------------------------------*/

#define BTOR_MEM_MGR_SAT(SMGR) ((SMGR)->mm)
#define BTOR_GET_SOLVER_SAT(SMGR) ((SMGR)->solver)

/*------------------------------------------------------------------------*/

/* Creates new SAT manager.
 * A SAT manager is used by nearly all functions of the SAT layer.
 */
BtorSATMgr *btor_new_sat_mgr (BtorMemMgr *mm, BtorMsg *msg);

bool btor_has_clone_support_sat_mgr (BtorSATMgr *smgr);

bool btor_has_term_support_sat_mgr (BtorSATMgr *smgr);

void btor_set_term_sat_mgr (BtorSATMgr *smgr, int (*fun) (void *), void *state);

/* Clones existing SAT manager (and underlying SAT solver). */
BtorSATMgr *btor_clone_sat_mgr (BtorMemMgr *mm, BtorMsg *msg, BtorSATMgr *smgr);

BtorMemMgr *btor_mem_mgr_sat (BtorSATMgr *smgr);

void *btor_get_solver_sat (BtorSATMgr *smgr);

/* Returns if the SAT solver has already been initialized */
int btor_is_initialized_sat (BtorSATMgr *smgr);

/* Deletes SAT manager from memory. */
void btor_delete_sat_mgr (BtorSATMgr *smgr);

/* Generates fresh CNF indices.
 * Indices are generated in consecutive order. */
int btor_next_cnf_id_sat_mgr (BtorSATMgr *smgr);

/* Mark old CNF index as not used anymore. */
void btor_release_cnf_id_sat_mgr (BtorSATMgr *smgr, int);

/* Returns the last CNF index that has been generated. */
int btor_get_last_cnf_id_sat_mgr (BtorSATMgr *smgr);

/* Inits the SAT solver. */
void btor_init_sat (BtorSATMgr *smgr);

/* Sets the output file of the SAT solver. */
void btor_set_output_sat (BtorSATMgr *smgr, FILE *output);

/* Prints statistics of SAT solver. */
void btor_print_stats_sat (BtorSATMgr *smgr);

/* Adds literal to the current clause of the SAT solver.
 * 0 terminates the current clause.
 */
void btor_add_sat (BtorSATMgr *smgr, int lit);

/* Adds assumption to SAT solver.
 * Requires that SAT solver supports this.
 */
void btor_assume_sat (BtorSATMgr *smgr, int lit);

/* Checks whether an assumption failed during
 * the last SAT solver call 'btor_sat_sat'.
 */
int btor_failed_sat (BtorSATMgr *smgr, int lit);

/* Solves the SAT instance.
 * limit < 0 -> no limit.
 */
BtorSolverResult btor_sat_sat (BtorSATMgr *smgr, int limit);

/* Gets assignment of a literal (in the SAT case).
 * Do not call before calling btor_sat_sat.
 */
int btor_deref_sat (BtorSATMgr *smgr, int lit);

/* Gets equivalence class represenative of a literal
 * or the literal itself if it is in a singleton
 * equivalence, fixed or eliminated.
 * Do not call before calling btor_sat_sat.
 */
int btor_repr_sat (BtorSATMgr *smgr, int lit);

/* Gets assignment of a literal (in the SAT case)
 * similar to 'deref', but only consider top level.
 * Do not call before calling btor_sat_sat.
 */
int btor_fixed_sat (BtorSATMgr *smgr, int lit);

/* Resets the status of the SAT solver. */
void btor_reset_sat (BtorSATMgr *smgr);

/* Determines if assignments have been changed
 * as constraints have been added.
 */
int btor_changed_sat (BtorSATMgr *smgr);

/* Determine wether SAT solver is already inconsistent.
 */
int btor_inconsistent_sat (BtorSATMgr *smgr);

#ifdef BTOR_USE_PICOSAT
/* Enables PicoSAT as SAT preprocessor. */
void btor_enable_picosat_sat (BtorSATMgr *smgr);
#endif

#ifdef BTOR_USE_LINGELING
/* Enables Lingeling as SAT preprocessor. */
int btor_enable_lingeling_sat (BtorSATMgr *smgr,
                               const char *options,
                               bool fork);
#endif

#ifdef BTOR_USE_MINISAT
/* Enables MiniSAT as SAT preprocessor. */
void btor_enable_minisat_sat (BtorSATMgr *smgr);
#endif

#endif
