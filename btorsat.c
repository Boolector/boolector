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

#ifdef BTOR_USE_PICOSAT
#include "../picosat/picosat.h"
#endif

#ifdef BTOR_USE_PRECOSAT
#include "btorpreco.h"
#endif

#ifdef BTOR_USE_LINGELING
#include "../lingeling/lglib.h"
#endif

#ifdef BTOR_USE_MINISAT
#include "btorminisat.h"
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

/*------------------------------------------------------------------------*/
/* END OF DECLARATIONS                                                    */
/*------------------------------------------------------------------------*/

/*------------------------------------------------------------------------*/
/* BEGIN OF IMPLEMENTATION                                                */
/*------------------------------------------------------------------------*/
/*------------------------------------------------------------------------*/
/* Auxilliary                                                             */
/*------------------------------------------------------------------------*/

void
btor_msg_sat (BtorSATMgr *smgr, int level, const char *fmt, ...)
{
  va_list ap;
  if (smgr->verbosity < level) return;
  assert (fmt != NULL);
  fprintf (stdout, "[btorsat] ");
  va_start (ap, fmt);
  vfprintf (stdout, fmt, ap);
  va_end (ap);
  putc ('\n', stdout);
  fflush (stdout);
}

/*------------------------------------------------------------------------*/
/* BtorSAT                                                                */
/*------------------------------------------------------------------------*/

#ifdef BTOR_USE_LINGELING
void btor_enable_lingeling_sat (BtorSATMgr *);
#define btor_enable_default_sat btor_enable_lingeling_sat
#else
#ifndef BTOR_USE_PICOSAT
#error "can not compile without incremental SAT solver"
#endif
void btor_enable_picosat_sat (BtorSATMgr *);
#define btor_enable_default_sat btor_enable_picosat_sat
#endif

/*------------------------------------------------------------------------*/

BtorSATMgr *
btor_new_sat_mgr (BtorMemMgr *mm)
{
  BtorSATMgr *smgr;

  assert (mm != NULL);

  BTOR_NEW (mm, smgr);

  smgr->verbosity   = 0;
  smgr->mm          = mm;
  smgr->inc.need    = 1;
  smgr->satcalls    = 0;
  smgr->initialized = 0;
  smgr->clauses = smgr->maxvar = 0;
  smgr->output                 = stdout;

  btor_enable_default_sat (smgr);

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
  result = smgr->api.inc_max_var (smgr);
  if (abs (result) > smgr->maxvar) smgr->maxvar = abs (result);
  BTOR_ABORT_SAT (result <= 0, "CNF id overflow");
  if (smgr->verbosity > 2 && !(result % 100000))
    btor_msg_sat (smgr, 2, "reached CNF id %d", result);
  return result;
}

void
btor_release_cnf_id_sat_mgr (BtorSATMgr *smgr, int lit)
{
  assert (smgr);
  if (!smgr->initialized) return;
  // TODO remove?
  // assert ((smgr->inc.need && smgr->inc.provides) || !smgr->satcalls);
  assert (abs (lit) <= smgr->maxvar);
  if (abs (lit) == smgr->true_lit) return;
  if (smgr->inc.api.melt) smgr->inc.api.melt (smgr, lit);
}

int
btor_get_last_cnf_id_sat_mgr (BtorSATMgr *smgr)
{
  assert (smgr != NULL);
  assert (smgr->initialized);
  (void) smgr;
  return smgr->api.variables (smgr);
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

/*------------------------------------------------------------------------*/

void
btor_init_sat (BtorSATMgr *smgr, int incremental)
{
  assert (smgr != NULL);
  assert (!smgr->initialized);

  smgr->solver      = smgr->api.init (smgr);
  smgr->initialized = 1;

  if (incremental)
  {
    assert (smgr->inc.provides);
    assert (smgr->inc.need);
  }
  else
  {
    btor_msg_sat (smgr, 1, "switching to non-incremental mode");
    smgr->inc.need = 0;
  }

  smgr->true_lit = btor_next_cnf_id_sat_mgr (smgr);
  btor_add_sat (smgr, smgr->true_lit);
  btor_add_sat (smgr, 0);
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
  smgr->api.set_output (smgr, output);
  smgr->output = output;

  prefix = btor_malloc (smgr->mm, strlen (smgr->name) + 4);
  sprintf (prefix, "[%s] ", smgr->name);
  q = prefix + 1;
  for (p = smgr->name; *p; p++) *q++ = tolower (*p);
  smgr->api.set_prefix (smgr, prefix);
  btor_free (smgr->mm, prefix, strlen (smgr->name) + 4);
}

void
btor_enable_verbosity_sat (BtorSATMgr *smgr)
{
  assert (smgr != NULL);
  assert (smgr->initialized);
  (void) smgr;
  smgr->api.enable_verbosity (smgr);
}

void
btor_print_stats_sat (BtorSATMgr *smgr)
{
  assert (smgr != NULL);
  if (!smgr->initialized) return;
  smgr->api.stats (smgr);
}

void
btor_add_sat (BtorSATMgr *smgr, int lit)
{
  assert (smgr != NULL);
  assert (smgr->initialized);
  assert ((smgr->inc.need && smgr->inc.provides) || !smgr->satcalls);
  assert (abs (lit) <= smgr->maxvar);
  if (!lit) smgr->clauses++;
  (void) smgr->api.add (smgr, lit);
}

int
btor_sat_sat (BtorSATMgr *smgr, int limit)
{
  assert (smgr != NULL);
  assert (smgr->initialized);
  btor_msg_sat (smgr, 2, "calling SAT solver %s", smgr->name);
  smgr->satcalls++;
  return smgr->api.sat (smgr, limit);
}

int
btor_deref_sat (BtorSATMgr *smgr, int lit)
{
  (void) smgr;
  assert (smgr != NULL);
  assert (smgr->initialized);
  assert (abs (lit) <= smgr->maxvar);
  return smgr->api.deref (smgr, lit);
}

void
btor_reset_sat (BtorSATMgr *smgr)
{
  assert (smgr != NULL);
  assert (smgr->initialized);
  btor_msg_sat (smgr, 2, "resetting %s", smgr->name);
  smgr->api.reset (smgr);
  smgr->solver      = 0;
  smgr->initialized = 0;
}

int
btor_provides_incremental_sat (BtorSATMgr *smgr)
{
  assert (smgr != NULL);
  return smgr->inc.provides;
}

int
btor_fixed_sat (BtorSATMgr *smgr, int lit)
{
  int res;
  assert (smgr != NULL);
  assert (smgr->initialized);
  assert (abs (lit) <= smgr->maxvar);
  res = smgr->api.fixed (smgr, lit);
  return res;
}

/*------------------------------------------------------------------------*/

void
btor_assume_sat (BtorSATMgr *smgr, int lit)
{
  assert (smgr != NULL);
  assert (smgr->initialized);
  assert (abs (lit) <= smgr->maxvar);
  assert (smgr->inc.need);
  assert (smgr->inc.provides);
  smgr->inc.api.assume (smgr, lit);
}

int
btor_failed_sat (BtorSATMgr *smgr, int lit)
{
  (void) smgr;
  assert (smgr != NULL);
  assert (smgr->initialized);
  assert (abs (lit) <= smgr->maxvar);
  assert (smgr->inc.need);
  assert (smgr->inc.provides);
  return smgr->inc.api.failed (smgr, lit);
}

int
btor_inconsistent_sat (BtorSATMgr *smgr)
{
  (void) smgr;
  assert (smgr != NULL);
  assert (smgr->initialized);
  assert (smgr->inc.need);
  assert (smgr->inc.provides);
  return smgr->inc.api.inconsistent (smgr);
}

int
btor_changed_sat (BtorSATMgr *smgr)
{
  (void) smgr;
  assert (smgr != NULL);
  assert (smgr->initialized);
  assert (smgr->inc.need);
  assert (smgr->inc.provides);
  return smgr->inc.api.changed (smgr);
}

/*------------------------------------------------------------------------*/

#ifdef BTOR_USE_PRECOSAT

void
btor_enable_precosat_sat (BtorSATMgr *smgr)
{
  assert (smgr != NULL);

  BTOR_ABORT_SAT (smgr->initialized,
                  "'btor_init_sat' called before "
                  "'btor_enable_precosat_sat'");

  smgr->name = "PrecoSAT";

  smgr->api.init             = btor_precosat_init;
  smgr->api.add              = btor_precosat_add;
  smgr->api.sat              = btor_precosat_sat;
  smgr->api.deref            = btor_precosat_deref;
  smgr->api.reset            = btor_precosat_reset;
  smgr->api.set_output       = btor_precosat_set_output;
  smgr->api.set_prefix       = btor_precosat_set_prefix;
  smgr->api.enable_verbosity = btor_precosat_enable_verbosity;
  smgr->api.inc_max_var      = btor_precosat_inc_max_var;
  smgr->api.variables        = btor_precosat_variables;
  smgr->api.stats            = btor_precosat_stats;

  memset (&smgr->inc, 0, sizeof smgr->inc);

  btor_msg_sat (smgr, 1, "PrecoSAT allows only non-incremental mode");
}
#endif

/*------------------------------------------------------------------------*/

#ifdef BTOR_USE_PICOSAT

static void *
btor_picosat_init (BtorSATMgr *smgr)
{
  btor_msg_sat (smgr, 1, "PicoSAT Version %s", picosat_version ());

  picosat_set_new (smgr->mm, (void *(*) (void *, size_t)) btor_malloc);
  picosat_set_delete (smgr->mm, (void (*) (void *, void *, size_t)) btor_free);
  picosat_set_resize (
      smgr->mm, (void *(*) (void *, void *, size_t, size_t)) btor_realloc);

  picosat_init ();
  picosat_set_global_default_phase (0);

  return 0;
}

static void
btor_picosat_add (BtorSATMgr *smgr, int lit)
{
  (void) smgr;
  (void) picosat_add (lit);
}

static int
btor_picosat_sat (BtorSATMgr *smgr, int limit)
{
  (void) smgr;
  return picosat_sat (limit);
}

static int
btor_picosat_changed (BtorSATMgr *smgr)
{
  (void) smgr;
  return picosat_changed ();
}

static int
btor_picosat_deref (BtorSATMgr *smgr, int lit)
{
  (void) smgr;
  return picosat_deref (lit);
}

static void
btor_picosat_reset (BtorSATMgr *smgr)
{
  (void) smgr;
  picosat_reset ();
}

static void
btor_picosat_set_output (BtorSATMgr *smgr, FILE *output)
{
  (void) smgr;
  picosat_set_output (output);
}

static void
btor_picosat_set_prefix (BtorSATMgr *smgr, const char *prefix)
{
  (void) smgr;
  picosat_set_prefix (prefix);
}

static void
btor_picosat_enable_verbosity (BtorSATMgr *smgr)
{
  (void) smgr;
  picosat_set_verbosity (1);
}

static int
btor_picosat_inc_max_var (BtorSATMgr *smgr)
{
  (void) smgr;
  return picosat_inc_max_var ();
}

static int
btor_picosat_variables (BtorSATMgr *smgr)
{
  (void) smgr;
  return picosat_variables ();
}

static void
btor_picosat_stats (BtorSATMgr *smgr)
{
  (void) smgr;
  picosat_stats ();
}

static int
btor_picosat_fixed (BtorSATMgr *smgr, int lit)
{
  int res;
  (void) smgr;
  res = picosat_deref_toplevel (lit);
  return res;
}

/*------------------------------------------------------------------------*/

static void
btor_picosat_assume (BtorSATMgr *smgr, int lit)
{
  (void) smgr;
  (void) picosat_assume (lit);
}

static int
btor_picosat_failed (BtorSATMgr *smgr, int lit)
{
  (void) smgr;
  return picosat_failed_assumption (lit);
}

static int
btor_picosat_inconsistent (BtorSATMgr *smgr)
{
  (void) smgr;
  return picosat_inconsistent ();
}

/*------------------------------------------------------------------------*/

void
btor_enable_picosat_sat (BtorSATMgr *smgr)
{
  assert (smgr != NULL);

  BTOR_ABORT_SAT (smgr->initialized,
                  "'btor_init_sat' called before 'btor_enable_picosat_sat'");

  smgr->name = "PicoSAT";

  smgr->api.init             = btor_picosat_init;
  smgr->api.add              = btor_picosat_add;
  smgr->api.sat              = btor_picosat_sat;
  smgr->api.deref            = btor_picosat_deref;
  smgr->api.reset            = btor_picosat_reset;
  smgr->api.set_output       = btor_picosat_set_output;
  smgr->api.set_prefix       = btor_picosat_set_prefix;
  smgr->api.enable_verbosity = btor_picosat_enable_verbosity;
  smgr->api.inc_max_var      = btor_picosat_inc_max_var;
  smgr->api.variables        = btor_picosat_variables;
  smgr->api.stats            = btor_picosat_stats;

  smgr->inc.provides         = 1;
  smgr->inc.api.assume       = btor_picosat_assume;
  smgr->inc.api.melt         = 0;
  smgr->inc.api.failed       = btor_picosat_failed;
  smgr->inc.api.fixed        = btor_picosat_fixed;
  smgr->inc.api.inconsistent = btor_picosat_inconsistent;
  smgr->inc.api.changed      = btor_picosat_changed;

  btor_msg_sat (
      smgr, 1, "PicoSAT allows both incremental and non-incremental mode");
}

#endif

/*------------------------------------------------------------------------*/

#ifdef BTOR_USE_LINGELING

static void
btor_lingeling_set_opt (LGL *lgl, const char *name, int val)
{
  if (lglhasopt (lgl, name)) lglsetopt (lgl, name, val);
}

static void *
btor_lingeling_init (BtorSATMgr *smgr)
{
  LGL *res;
  if (smgr->verbosity >= 1)
  {
    lglbnr ("Lingeling", "[lingeling] ", stdout);
    fflush (stdout);
  }
  res                    = lglminit (smgr->mm,
                  (lglalloc) btor_malloc,
                  (lglrealloc) btor_realloc,
                  (lgldealloc) btor_free);
  smgr->lingeling.forked = 0;
  return res;
}

static void
btor_lingeling_add (BtorSATMgr *smgr, int lit)
{
  lgladd (smgr->solver, lit);
}

static int
btor_lingeling_sat (BtorSATMgr *smgr, int limit)
{
  char name[80];
  LGL *forked;
  int res;
  if (limit >= 200)
  {
    forked = lglfork (smgr->solver);
    sprintf (name, "[lingeling-fork-%d] ", smgr->lingeling.forked++);
    lglsetprefix (forked, name);
    lglsetout (forked, smgr->output);
    if (lglgetopt (smgr->solver, "verbose")) lglsetopt (forked, "verbose", 1);
    btor_lingeling_set_opt (forked, "clim", limit);
    res = lglsat (forked);
    lgljoin (smgr->solver, forked);
  }
  else
  {
    btor_lingeling_set_opt (smgr->solver, "clim", limit);
    res = lglsat (smgr->solver);
  }
  return res;
}

static int
btor_lingeling_changed (BtorSATMgr *smgr)
{
  return lglchanged (smgr->solver);
}

static int
btor_lingeling_deref (BtorSATMgr *smgr, int lit)
{
  return lglderef (smgr->solver, lit);
}

static void
btor_lingeling_reset (BtorSATMgr *smgr)
{
  lglrelease (smgr->solver);
}

static void
btor_lingeling_set_output (BtorSATMgr *smgr, FILE *output)
{
  lglsetout (smgr->solver, output);
}

static void
btor_lingeling_set_prefix (BtorSATMgr *smgr, const char *prefix)
{
  lglsetprefix (smgr->solver, prefix);
}

static void
btor_lingeling_enable_verbosity (BtorSATMgr *smgr)
{
  lglsetopt (smgr->solver, "verbose", 1);
}

static int
btor_lingeling_inc_max_var (BtorSATMgr *smgr)
{
  int res = lglincvar (smgr->solver);
  // TODO what about this?
  // if (smgr->inc.need)
  lglfreeze (smgr->solver, res);
  return res;
}

static int
btor_lingeling_variables (BtorSATMgr *smgr)
{
  return lglmaxvar (smgr->solver);
}

static void
btor_lingeling_stats (BtorSATMgr *smgr)
{
  lglstats (smgr->solver);
}

/*------------------------------------------------------------------------*/

static void
btor_lingeling_assume (BtorSATMgr *smgr, int lit)
{
  lglassume (smgr->solver, lit);
}

static void
btor_lingeling_melt (BtorSATMgr *smgr, int lit)
{
  if (smgr->inc.need) lglmelt (smgr->solver, lit);
}

static int
btor_lingeling_failed (BtorSATMgr *smgr, int lit)
{
  return lglfailed (smgr->solver, lit);
}

static int
btor_lingeling_fixed (BtorSATMgr *smgr, int lit)
{
  return lglfixed (smgr->solver, lit);
}

static int
btor_lingeling_inconsistent (BtorSATMgr *smgr)
{
  return lglinconsistent (smgr->solver);
}

/*------------------------------------------------------------------------*/

void
btor_enable_lingeling_sat (BtorSATMgr *smgr)
{
  assert (smgr != NULL);

  BTOR_ABORT_SAT (smgr->initialized,
                  "'btor_init_sat' called before 'btor_enable_lingeling_sat'");

  smgr->name = "Lingeling";

  smgr->api.init             = btor_lingeling_init;
  smgr->api.add              = btor_lingeling_add;
  smgr->api.sat              = btor_lingeling_sat;
  smgr->api.deref            = btor_lingeling_deref;
  smgr->api.fixed            = btor_lingeling_fixed;
  smgr->api.reset            = btor_lingeling_reset;
  smgr->api.set_output       = btor_lingeling_set_output;
  smgr->api.set_prefix       = btor_lingeling_set_prefix;
  smgr->api.enable_verbosity = btor_lingeling_enable_verbosity;
  smgr->api.inc_max_var      = btor_lingeling_inc_max_var;
  smgr->api.variables        = btor_lingeling_variables;
  smgr->api.stats            = btor_lingeling_stats;

  smgr->inc.provides         = 1;
  smgr->inc.api.assume       = btor_lingeling_assume;
  smgr->inc.api.melt         = btor_lingeling_melt;
  smgr->inc.api.failed       = btor_lingeling_failed;
  smgr->inc.api.inconsistent = btor_lingeling_inconsistent;
  smgr->inc.api.changed      = btor_lingeling_changed;

  btor_msg_sat (
      smgr, 1, "Lingeling allows both incremental and non-incremental mode");
}
#endif

/*------------------------------------------------------------------------*/

#ifdef BTOR_USE_MINISAT

/*------------------------------------------------------------------------*/

void
btor_enable_minisat_sat (BtorSATMgr *smgr)
{
  assert (smgr != NULL);

  BTOR_ABORT_SAT (smgr->initialized,
                  "'btor_init_sat' called before 'btor_enable_minisat_sat'");

  smgr->name = "MiniSAT";

  smgr->api.init             = btor_minisat_init;
  smgr->api.add              = btor_minisat_add;
  smgr->api.sat              = btor_minisat_sat;
  smgr->api.deref            = btor_minisat_deref;
  smgr->api.fixed            = btor_minisat_fixed;
  smgr->api.reset            = btor_minisat_reset;
  smgr->api.set_output       = btor_minisat_set_output;
  smgr->api.set_prefix       = btor_minisat_set_prefix;
  smgr->api.enable_verbosity = btor_minisat_enable_verbosity;
  smgr->api.inc_max_var      = btor_minisat_inc_max_var;
  smgr->api.variables        = btor_minisat_variables;
  smgr->api.stats            = btor_minisat_stats;

  smgr->inc.provides         = 1;
  smgr->inc.api.assume       = btor_minisat_assume;
  smgr->inc.api.melt         = 0;
  smgr->inc.api.failed       = btor_minisat_failed;
  smgr->inc.api.inconsistent = btor_minisat_inconsistent;
  smgr->inc.api.changed      = btor_minisat_changed;

  btor_msg_sat (
      smgr, 1, "MiniSAT allows both incremental and non-incremental mode");
}

#endif

/*------------------------------------------------------------------------*/
/* END OF IMPLEMENTATION                                                  */
/*------------------------------------------------------------------------*/
