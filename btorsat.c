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

#define BTOR_ABORT_SAT(cond, msg)          \
  do                                       \
  {                                        \
    if (!(cond)) break;                    \
    fputs ("[btorsat] " msg "\n", stdout); \
    exit (BTOR_ERR_EXIT);                  \
  } while (0)

struct BtorSATMgr
{
  int verbosity;
  BtorMemMgr *mm;
  int initialized;
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

  smgr->verbosity   = 0;
  smgr->mm          = mm;
  smgr->initialized = 0;

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
  result = picosat_inc_max_var ();
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
  return picosat_variables ();
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
    fprintf (stdout, "[btorsat] PicoSAT Version %s\n", picosat_version ());

    fflush (stdout);
  }

  picosat_set_new (smgr->mm, (void *(*) (void *, size_t)) btor_malloc);
  picosat_set_delete (smgr->mm, (void (*) (void *, void *, size_t)) btor_free);
  picosat_set_resize (
      smgr->mm, (void *(*) (void *, void *, size_t, size_t)) btor_realloc);

  if (smgr->verbosity >= 3) picosat_measure_all_calls ();

  picosat_init ();

  smgr->initialized = 1;
}

void
btor_set_output_sat (BtorSATMgr *smgr, FILE *output)
{
  assert (smgr != NULL);
  assert (smgr->initialized);
  assert (output != NULL);
  (void) smgr;
  picosat_set_output (output);
  picosat_set_prefix ("[picosat] ");
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
  picosat_stats ();
}

void
btor_add_sat (BtorSATMgr *smgr, int lit)
{
  assert (smgr != NULL);
  assert (smgr->initialized);
  (void) smgr;
  picosat_add (lit);
#if 0
  if (lit != 0)
    printf ("%d ", lit);
  else
    printf ("0\n");
#endif
}

void
btor_dump_cnf_sat (BtorSATMgr *smgr, FILE *output)
{
  assert (smgr != NULL);
  assert (output != NULL);
  assert (smgr->initialized);
  (void) smgr;
  picosat_print (output);
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
  if (smgr->verbosity > 2) print_verbose_msg ("calling SAT solver PicoSAT\n");
  return picosat_sat (limit);
}

int
btor_deref_sat (BtorSATMgr *smgr, int lit)
{
  assert (smgr != NULL);
  assert (smgr->initialized);
  (void) smgr;
  return picosat_deref (lit);
}

void
btor_reset_sat (BtorSATMgr *smgr)
{
  assert (smgr != NULL);
  assert (smgr->initialized);
  (void) smgr;
  if (smgr->verbosity > 1) print_verbose_msg ("resetting PicoSAT\n");
  picosat_reset ();
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

/*------------------------------------------------------------------------*/
/* END OF IMPLEMENTATION                                                  */
/*------------------------------------------------------------------------*/
