/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2010 Robert Daniel Brummayer, FMV, JKU.
 *  Copyright (C) 2010-2011 Armin Biere, FMV, JKU.
 *
 *  This file is part of Boolector.
 *
 *  Boolector is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation, either version 3 of the License, or
 *  (at your option) any later version.
 *
 *  Boolector is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

#include "../picosat/picosat.h"

#ifdef BTOR_USE_PRECOSAT
#include "btorpreco.h"
#endif

#ifdef BTOR_USE_LINGELING
#include "../lingeling/lglib.h"
#endif

#include "btorexit.h"
#include "btorsat.h"

#include <assert.h>
#include <ctype.h>
#include <limits.h>
#include <stdarg.h>
#include <stdlib.h>

/*------------------------------------------------------------------------*/
/* BEGIN OF DECLARATIONS                                                  */
/*------------------------------------------------------------------------*/
/*------------------------------------------------------------------------*/
/* BtorSATMgr                                                             */
/*------------------------------------------------------------------------*/

#define BTOR_ABORT_SAT(cond, msg)                   \
  do                                                \
  {                                                 \
    if (cond)                                       \
    {                                               \
      printf ("[btorsat] %s: %s\n", __func__, msg); \
      fflush (stdout);                              \
      exit (BTOR_ERR_EXIT);                         \
    }                                               \
  } while (0)

struct BtorSATMgr
{
  void *solver;

  int verbosity;
  BtorMemMgr *mm;
  int initialized;
  int preproc_enabled;

  FILE *output;

  const char *ss_name;

  void *(*ss_init) ();
  int (*ss_add) (void *, int);
  int (*ss_sat) (void *);
  int (*ss_deref) (void *, int);
  void (*ss_reset) (void *);
  void (*ss_set_output) (void *, FILE *);
  void (*ss_set_prefix) (void *, const char *);
  void (*ss_enable_verbosity) (void *);
  int (*ss_inc_max_var) (void *);
  int (*ss_variables) (void *);
  int (*ss_clauses) (void *);
  void (*ss_set_new) (void *, void *, void *(*) (void *, size_t));
  void (*ss_set_delete) (void *, void *, void (*) (void *, void *, size_t));
  void (*ss_set_resize) (void *,
                         void *,
                         void *(*) (void *, void *, size_t, size_t));
  void (*ss_stats) (void *);
};

/*------------------------------------------------------------------------*/
/* END OF DECLARATIONS                                                    */
/*------------------------------------------------------------------------*/

/*------------------------------------------------------------------------*/
/* BEGIN OF IMPLEMENTATION                                                */
/*------------------------------------------------------------------------*/
/*------------------------------------------------------------------------*/
/* Auxilliary                                                             */
/*------------------------------------------------------------------------*/

static void
btor_msg_sat (const char *fmt, ...)
{
  va_list ap;
  assert (fmt != NULL);
  fprintf (stdout, "[btorsat] ");
  va_start (ap, fmt);
  vfprintf (stdout, fmt, ap);
  va_end (ap);
  fflush (stdout);
}

static void *
btor_picosat_init (void)
{
  picosat_init ();
  picosat_set_global_default_phase (0);
  return 0;
}

static int
btor_picosat_add (void *dummy, int lit)
{
  (void) dummy;
  (void) picosat_add (lit);
  return 0;
}

static int
btor_picosat_sat (void *dummy)
{
  (void) dummy;
  return picosat_sat (-1);
}

static int
btor_picosat_deref (void *dummy, int lit)
{
  (void) dummy;
  return picosat_deref (lit);
}

static void
btor_picosat_reset (void *dummy)
{
  (void) dummy;
  picosat_reset ();
}

static void
btor_picosat_set_output (void *dummy, FILE *output)
{
  (void) dummy;
  picosat_set_output (output);
}

static void
btor_picosat_set_prefix (void *dummy, const char *prefix)
{
  (void) dummy;
  picosat_set_prefix (prefix);
}

static void
btor_picosat_enable_verbosity (void *dummy)
{
  (void) dummy;
  picosat_set_verbosity (1);
}

static int
btor_picosat_inc_max_var (void *dummy)
{
  (void) dummy;
  return picosat_inc_max_var ();
}

static int
btor_picosat_variables (void *dummy)
{
  (void) dummy;
  return picosat_variables ();
}

static int
btor_picosat_clauses (void *dummy)
{
  (void) dummy;
  return picosat_added_original_clauses ();
}

static void
btor_picosat_set_new (void *dummy,
                      void *memmgr,
                      void *(*newfun) (void *, size_t))
{
  (void) dummy;
  picosat_set_new (memmgr, newfun);
}

static void
btor_picosat_set_delete (void *dummy,
                         void *memmgr,
                         void (*delfun) (void *, void *, size_t))
{
  (void) dummy;
  picosat_set_delete (memmgr, delfun);
}

static void
btor_picosat_set_resize (void *dummy,
                         void *memmgr,
                         void *(*rszfun) (void *, void *, size_t, size_t))
{
  (void) dummy;
  picosat_set_resize (memmgr, rszfun);
}

static void
btor_picosat_stats (void *dummy)
{
  (void) dummy;
  picosat_stats ();
}

/*------------------------------------------------------------------------*/
/* BtorSAT                                                                */
/*------------------------------------------------------------------------*/

BtorSATMgr *
btor_new_sat_mgr (BtorMemMgr *mm)
{
  BtorSATMgr *smgr;

  assert (mm != NULL);

  BTOR_NEW (mm, smgr);

  smgr->verbosity       = 0;
  smgr->mm              = mm;
  smgr->initialized     = 0;
  smgr->preproc_enabled = 0;

  smgr->ss_name = "PicoSAT";

  smgr->ss_init             = btor_picosat_init;
  smgr->ss_add              = btor_picosat_add;
  smgr->ss_sat              = btor_picosat_sat;
  smgr->ss_deref            = btor_picosat_deref;
  smgr->ss_reset            = btor_picosat_reset;
  smgr->ss_set_output       = btor_picosat_set_output;
  smgr->ss_set_prefix       = btor_picosat_set_prefix;
  smgr->ss_enable_verbosity = btor_picosat_enable_verbosity;
  smgr->ss_inc_max_var      = btor_picosat_inc_max_var;
  smgr->ss_variables        = btor_picosat_variables;
  smgr->ss_clauses          = btor_picosat_clauses;
  smgr->ss_set_new          = btor_picosat_set_new;
  smgr->ss_set_delete       = btor_picosat_set_delete;
  smgr->ss_set_resize       = btor_picosat_set_resize;
  smgr->ss_stats            = btor_picosat_stats;

  return smgr;
}

void
btor_set_verbosity_sat_mgr (BtorSATMgr *smgr, int verbosity)
{
  assert (verbosity >= -1 && verbosity <= 3);
  smgr->verbosity = verbosity;
}

int
btor_is_initialized_sat (BtorSATMgr *smgr)
{
  assert (smgr != NULL);
  return smgr->initialized;
}

int
btor_next_cnf_id_sat_mgr (BtorSATMgr *smgr)
{
  int result;
  assert (smgr);
  assert (smgr->initialized);
  (void) smgr;
  result = smgr->ss_inc_max_var (smgr->solver);
  BTOR_ABORT_SAT (result <= 0, "CNF id overflow");
  if (smgr->verbosity > 2 && !(result % 100000))
    btor_msg_sat ("reached CNF id %d\n", result);
  return result;
}

int
btor_get_last_cnf_id_sat_mgr (BtorSATMgr *smgr)
{
  assert (smgr != NULL);
  assert (smgr->initialized);
  (void) smgr;
  return smgr->ss_variables (smgr->solver);
}

void
btor_delete_sat_mgr (BtorSATMgr *smgr)
{
  assert (smgr != NULL);
  /* if SAT is still initialized, then
   * reset_sat has not been called
   */
  if (smgr->initialized) btor_reset_sat (smgr);
  BTOR_DELETE (smgr->mm, smgr);
}

void
btor_init_sat (BtorSATMgr *smgr)
{
  assert (smgr != NULL);
  assert (!smgr->initialized);

  if (smgr->verbosity > 0)
  {
#ifdef BTOR_USE_LINGELING
    if (1)
      btor_msg_sat ("Lingeling Version %s\n", lglversion ());
    else
#endif
#ifdef BTOR_USE_PRECOSAT
        if (smgr->preproc_enabled)
      btor_msg_sat ("PrecoSAT Version %s\n", btor_precosat_version ());
    else
#endif
      btor_msg_sat ("PicoSAT Version %s\n", picosat_version ());
    fflush (stdout);
  }

  smgr->solver = smgr->ss_init ();

  smgr->ss_set_new (
      smgr->solver, smgr->mm, (void *(*) (void *, size_t)) btor_malloc);
  smgr->ss_set_delete (
      smgr->solver, smgr->mm, (void (*) (void *, void *, size_t)) btor_free);
  smgr->ss_set_resize (
      smgr->solver,
      smgr->mm,
      (void *(*) (void *, void *, size_t, size_t)) btor_realloc);

  smgr->initialized = 1;
}

void
btor_set_output_sat (BtorSATMgr *smgr, FILE *output)
{
  char *prefix, *q;
  const char *p;

  assert (smgr != NULL);
  assert (smgr->initialized);
  assert (output != NULL);
  (void) smgr;
  smgr->ss_set_output (smgr->solver, output);
  smgr->output = output;

  prefix = btor_malloc (smgr->mm, strlen (smgr->ss_name) + 4);
  sprintf (prefix, "[%s] ", smgr->ss_name);
  q = prefix + 1;
  for (p = smgr->ss_name; *p; p++) *q++ = tolower (*p);
  smgr->ss_set_prefix (smgr->solver, prefix);
  btor_free (smgr->mm, prefix, strlen (smgr->ss_name) + 4);
}

void
btor_enable_verbosity_sat (BtorSATMgr *smgr)
{
  assert (smgr != NULL);
  assert (smgr->initialized);
  (void) smgr;
  smgr->ss_enable_verbosity (smgr->solver);
}

void
btor_print_stats_sat (BtorSATMgr *smgr)
{
  assert (smgr != NULL);
  assert (smgr->initialized);
  (void) smgr;
  smgr->ss_stats (smgr->solver);
}

void
btor_add_sat (BtorSATMgr *smgr, int lit)
{
  assert (smgr != NULL);
  assert (smgr->initialized);
  (void) smgr;
  (void) smgr->ss_add (smgr->solver, lit);
}

void
btor_assume_sat (BtorSATMgr *smgr, int lit)
{
  assert (smgr != NULL);
  assert (smgr->initialized);
  (void) smgr;
  picosat_assume (lit);
}

int
btor_sat_sat (BtorSATMgr *smgr)
{
  assert (smgr != NULL);
  assert (smgr->initialized);
  (void) smgr;

  if (smgr->verbosity > 2)
  {
    btor_msg_sat ("calling SAT solver %s\n", smgr->ss_name);
    btor_msg_sat ("original clauses: %d\n", smgr->ss_clauses (smgr->solver));
  }

  return smgr->ss_sat (smgr->solver);
}

int
btor_deref_sat (BtorSATMgr *smgr, int lit)
{
  assert (smgr != NULL);
  assert (smgr->initialized);
  (void) smgr;
  return smgr->ss_deref (smgr->solver, lit);
}

void
btor_reset_sat (BtorSATMgr *smgr)
{
  assert (smgr != NULL);
  assert (smgr->initialized);
  (void) smgr;
  if (smgr->verbosity > 1) btor_msg_sat ("resetting %s\n", smgr->ss_name);
  smgr->ss_reset (smgr->solver);
  smgr->solver      = 0;
  smgr->initialized = 0;
}

int
btor_changed_assignments_sat (BtorSATMgr *smgr)
{
  assert (smgr != NULL);
  assert (smgr->initialized);
  (void) smgr;
  return picosat_changed ();
}

#ifdef BTOR_USE_PRECOSAT
void
btor_enable_precosat_sat (BtorSATMgr *smgr)
{
  assert (smgr != NULL);
  BTOR_ABORT_SAT (smgr->initialized,
                  "'btor_init_sat' called before "
                  "'btor_enable_precosat_sat'");
  smgr->ss_name             = "PrecoSAT";
  smgr->ss_init             = btor_precosat_init;
  smgr->ss_add              = btor_precosat_add;
  smgr->ss_sat              = btor_precosat_sat;
  smgr->ss_deref            = btor_precosat_deref;
  smgr->ss_reset            = btor_precosat_reset;
  smgr->ss_set_output       = btor_precosat_set_output;
  smgr->ss_set_prefix       = btor_precosat_set_prefix;
  smgr->ss_enable_verbosity = btor_precosat_enable_verbosity;
  smgr->ss_inc_max_var      = btor_precosat_inc_max_var;
  smgr->ss_variables        = btor_precosat_variables;
  smgr->ss_clauses          = btor_precosat_added_original_clauses;
  smgr->ss_set_new          = btor_precosat_set_new;
  smgr->ss_set_delete       = btor_precosat_set_delete;
  smgr->ss_set_resize       = btor_precosat_set_resize;
  smgr->ss_stats            = btor_precosat_stats;
  smgr->preproc_enabled     = 1;
}
#endif

#ifdef BTOR_USE_LINGELING

static void btor_lin

    void
    btor_enable_lingeling_sat (BtorSATMgr *smgr)
{
  assert (smgr != NULL);
  BTOR_ABORT_SAT (smgr->initialized,
                  "'btor_init_sat' called before "
                  "'btor_enable_lingeling_sat'");
  smgr->ss_name             = "Lingeling";
  smgr->ss_init             = btor_lingeling_init;
  smgr->ss_add              = btor_lingeling_add;
  smgr->ss_sat              = btor_lingeling_sat;
  smgr->ss_deref            = btor_lingeling_deref;
  smgr->ss_reset            = btor_lingeling_reset;
  smgr->ss_set_output       = btor_lingeling_set_output;
  smgr->ss_set_prefix       = btor_lingeling_set_prefix;
  smgr->ss_enable_verbosity = btor_lingeling_enable_verbosity;
  smgr->ss_inc_max_var      = btor_lingeling_inc_max_var;
  smgr->ss_variables        = btor_lingeling_variables;
  smgr->ss_clauses          = btor_lingeling_added_original_clauses;
  smgr->ss_set_new          = btor_lingeling_set_new;
  smgr->ss_set_delete       = btor_lingeling_set_delete;
  smgr->ss_set_resize       = btor_lingeling_set_resize;
  smgr->ss_stats            = btor_lingeling_stats;
  smgr->preproc_enabled     = 1;
}
#endif

/*------------------------------------------------------------------------*/
/* END OF IMPLEMENTATION                                                  */
/*------------------------------------------------------------------------*/
