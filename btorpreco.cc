#ifdef BTOR_USE_PRECOSAT
#include "../precosat/precobnr.hh"
#include "../precosat/precosat.hh"
extern "C" {
#include "btorpreco.h"
using namespace PrecoSat;
static Solver solver;

const char*
btor_precosat_version (void)
{
  return "btor_precosat_version not implemented yet";
}
};
#endif
