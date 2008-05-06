#include "../picoprep/picoprep.h"
#include "../picosat/picosat.h"

#include "btorexit.h"
#include "btorsat.h"

#include <assert.h>
#include <limits.h>
#include <stdarg.h>
#include <stdlib.h>

/*------------------------------------------------------------------------*/
/* BEGIN OF DECLARATIONS                                                  */
/*------------------------------------------------------------------------*/
/*------------------------------------------------------------------------*/
/* BtorSATMgr                                                             */
/*------------------------------------------------------------------------*/

#define BTOR_ABORT_SAT(cond, msg)            \
  do                                         \
  {                                          \
    if (cond)                                \
    {                                        \
      fputs ("[btorsat] " msg "\n", stdout); \
      exit (BTOR_ERR_EXIT);                  \
    }                                        \
  } while (0)

struct BtorSATMgr
{
  int verbosity;
  BtorMemMgr *mm;
  int initialized;
  int preproc_enabled;

  const char *ss_name;

  void (*ss_init) ();
  void (*ss_add) (int);
  int (*ss_sat) (int);
  int (*ss_deref) (int);
  void (*ss_reset) ();
  void (*ss_set_output) (FILE *);
  void (*ss_set_prefix) (const char *);
  int (*ss_inc_max_var) ();
  int (*ss_variables) ();
  void (*ss_set_new) (void *, void *(*) (void *, size_t));
  void (*ss_set_delete) (void *, void (*) (void *, void *, size_t));
  void (*ss_set_resize) (void *, void *(*) (void *, void *, size_t, size_t));
  void (*ss_stats) (void);
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
print_verbose_msg (const char *fmt, ...)
{
  va_list ap;
  assert (fmt != NULL);
  fprintf (stdout, "[btorsat] ");
  va_start (ap, fmt);
  vfprintf (stdout, fmt, ap);
  va_end (ap);
  fflush (stdout);
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

  smgr->ss_init        = picosat_init;
  smgr->ss_add         = picosat_add;
  smgr->ss_sat         = picosat_sat;
  smgr->ss_deref       = picosat_deref;
  smgr->ss_reset       = picosat_reset;
  smgr->ss_set_output  = picosat_set_output;
  smgr->ss_set_prefix  = picosat_set_prefix;
  smgr->ss_inc_max_var = picosat_inc_max_var;
  smgr->ss_variables   = picosat_variables;
  smgr->ss_set_new     = picosat_set_new;
  smgr->ss_set_delete  = picosat_set_delete;
  smgr->ss_set_resize  = picosat_set_resize;
  smgr->ss_stats       = picosat_stats;

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
  result = smgr->ss_inc_max_var ();
  BTOR_ABORT_SAT (result <= 0, "CNF id overflow");
  if (smgr->verbosity > 2 && !(result % 100000))
    print_verbose_msg ("reached CNF id %d\n", result);
  return result;
}

int
btor_get_last_cnf_id_sat_mgr (BtorSATMgr *smgr)
{
  assert (smgr != NULL);
  assert (smgr->initialized);
  (void) smgr;
  return smgr->ss_variables ();
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
    if (smgr->preproc_enabled)
      print_verbose_msg ("PicoPrep Version %s\n", picoprep_version ());

    print_verbose_msg ("PicoSAT  Version %s\n", picosat_version ());

    fflush (stdout);
  }

  smgr->ss_set_new (smgr->mm, (void *(*) (void *, size_t)) btor_malloc);
  smgr->ss_set_delete (smgr->mm, (void (*) (void *, void *, size_t)) btor_free);
  smgr->ss_set_resize (
      smgr->mm, (void *(*) (void *, void *, size_t, size_t)) btor_realloc);

  smgr->ss_init ();

  smgr->initialized = 1;
}

void
btor_set_output_sat (BtorSATMgr *smgr, FILE *output)
{
  char *prefix, *p, *q;

  assert (smgr != NULL);
  assert (smgr->initialized);
  assert (output != NULL);
  (void) smgr;
  smgr->ss_set_output (output);

  prefix = btor_malloc (smgr->mm, strlen (smgr->ss_name) + 3);
  sprintf (prefix, "[%s] ", smgr->ss_name);
  q = prefix + 1;
  for (p = smgr->ss_name; *p; p++) *q++ = tolower (*p);
  smgr->ss_set_prefix (prefix);
  btor_free (smgr->mm, prefix, strlen (smgr->ss_name) + 3);
}

void
btor_enable_verbosity_sat (BtorSATMgr *smgr)
{
  assert (smgr != NULL);
  assert (smgr->initialized);
  (void) smgr;
  picosat_enable_verbosity ();
}

void
btor_print_stats_sat (BtorSATMgr *smgr)
{
  assert (smgr != NULL);
  assert (smgr->initialized);
  (void) smgr;
  smgr->ss_stats ();
}

void
btor_add_sat (BtorSATMgr *smgr, int lit)
{
  assert (smgr != NULL);
  assert (smgr->initialized);
  (void) smgr;
  smgr->ss_add (lit);
#if 0
  if (lit != 0)
    printf ("%d ", lit);
  else
    printf ("0\n");
#endif
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
btor_sat_sat (BtorSATMgr *smgr, int limit)
{
  assert (smgr != NULL);
  assert (smgr->initialized);
  (void) smgr;
  if (smgr->verbosity > 2)
    print_verbose_msg ("calling SAT solver %s\n", smgr->ss_name);
  return smgr->ss_sat (limit);
}

int
btor_deref_sat (BtorSATMgr *smgr, int lit)
{
  assert (smgr != NULL);
  assert (smgr->initialized);
  (void) smgr;
  return smgr->ss_deref (lit);
}

void
btor_reset_sat (BtorSATMgr *smgr)
{
  assert (smgr != NULL);
  assert (smgr->initialized);
  (void) smgr;
  if (smgr->verbosity > 1) print_verbose_msg ("resetting %s\n", smgr->ss_name);
  smgr->ss_reset ();
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

void
btor_enable_preproc_sat (BtorSATMgr *smgr)
{
  assert (smgr != NULL);

  BTOR_ABORT_SAT (smgr->initialized,
                  "'btor_init_sat' called before "
                  "'btor_enable_preprocessor_sat'");

  smgr->ss_name = "PicoPrep";

  smgr->ss_init        = picoprep_init;
  smgr->ss_add         = picoprep_add;
  smgr->ss_sat         = picoprep_sat;
  smgr->ss_deref       = picoprep_deref;
  smgr->ss_reset       = picoprep_reset;
  smgr->ss_set_output  = picoprep_set_output;
  smgr->ss_set_prefix  = picoprep_set_prefix;
  smgr->ss_inc_max_var = picoprep_inc_max_var;
  smgr->ss_variables   = picoprep_variables;
  smgr->ss_set_new     = picoprep_set_new;
  smgr->ss_set_delete  = picoprep_set_delete;
  smgr->ss_set_resize  = picoprep_set_resize;
  smgr->ss_stats       = picoprep_stats;

  smgr->preproc_enabled = 1;
}
/*------------------------------------------------------------------------*/
/* END OF IMPLEMENTATION                                                  */
/*------------------------------------------------------------------------*/
