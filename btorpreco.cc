#ifdef BTOR_USE_PRECOSAT
#include "../precosat/precobnr.hh"
#include "../precosat/precosat.hh"
extern "C" {
#include "btorpreco.h"
using namespace PrecoSat;
static Solver *solver;
static void *(*new_for_precosat) (void *, size_t);
static void (*delete_for_precosat) (void *, void *, size_t);
static void *(*resize_for_precosat) (void *, void *, size_t, size_t);

const char *
btor_precosat_version (void)
{
  return "btor_precosat_version not implemented yet";
}

void
btor_precosat_init (void)
{
  assert (!solver);
  solver = new Solver ();
  assert (!new_for_precosat);
  assert (!delete_for_precosat);
  assert (!resize_for_precosat);
}

void
btor_precosat_reset (void)
{
  assert (solver);
  delete solver;
  solver = 0;
}
};
#endif
