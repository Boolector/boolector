#include "btorsat.h"
#include "../picosat/picosat.h"

#include <assert.h>
#include <limits.h>
#include <stdlib.h>

/*------------------------------------------------------------------------*/
/* BEGIN OF DECLARATIONS                                                  */
/*------------------------------------------------------------------------*/
/*------------------------------------------------------------------------*/
/* BtorCNFMgr                                                             */
/*------------------------------------------------------------------------*/

struct BtorCNFMgr
{
  int id;
  BtorMemMgr *mm;
};

/*------------------------------------------------------------------------*/
/* END OF DECLARATIONS                                                    */
/*------------------------------------------------------------------------*/

/*------------------------------------------------------------------------*/
/* BEGIN OF IMPLEMENTATION                                                */
/*------------------------------------------------------------------------*/

BtorCNFMgr *
btor_new_cnf_mgr (BtorMemMgr *mm)
{
  BtorCNFMgr *cmgr = NULL;
  assert (mm != NULL);
  cmgr     = (BtorCNFMgr *) btor_malloc (mm, sizeof (BtorCNFMgr));
  cmgr->id = 1;
  cmgr->mm = mm;
  return cmgr;
}

int
btor_next_cnf_id_cnf_mgr (BtorCNFMgr *cmgr)
{
  assert (cmgr != NULL);
  assert (cmgr->id < INT_MAX);
  return cmgr->id++;
}

void
btor_delete_cnf_mgr (BtorCNFMgr *cmgr)
{
  assert (cmgr != NULL);
  btor_free (cmgr->mm, cmgr, sizeof (BtorCNFMgr));
}

void
btor_init_sat (void)
{
  picosat_init ();
#if 0
  picosat_enable_verbosity ();
  picosat_set_output (stderr);
#endif
}

void
btor_add_sat (int lit)
{
  picosat_add (lit);
}

void
btor_dump_cnf_sat (FILE *output)
{
  assert (output != NULL);
  picosat_print (output);
}

void
btor_assume_sat (int lit)
{
  picosat_assume (lit);
}

int
btor_sat_sat (int limit)
{
  return picosat_sat (limit);
}

int
btor_deref_sat (int lit)
{
  return picosat_deref (lit);
}

void
btor_reset_sat (void)
{
  picosat_reset ();
}

/*------------------------------------------------------------------------*/
/* END OF IMPLEMENTATION                                                  */
/*------------------------------------------------------------------------*/
