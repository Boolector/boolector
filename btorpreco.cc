#ifdef BTOR_USE_PRECOSAT
#include "../precosat/precobnr.hh"
#include "../precosat/precosat.hh"
extern "C" {
#include "btorpreco.h"
using namespace PrecoSat;
static Solver *solver;
static void *emgr;
static void *(*new_for_precosat) (void *, size_t);
static void (*delete_for_precosat) (void *, void *, size_t);
static void *(*resize_for_precosat) (void *, void *, size_t, size_t);
static int added_original_clauses;

const char *
btor_precosat_version (void)
{
  return "btor_precosat_version not implemented yet";
}

void
btor_precosat_init (void)
{
  assert (!solver);
  solver = new Solver;
  assert (emgr);
  assert (new_for_precosat);
  assert (delete_for_precosat);
  assert (resize_for_precosat);
  solver->set (
      emgr, new_for_precosat, delete_for_precosat, resize_for_precosat);
  solver->init ();
  solver->fxopts ();
}

int
btor_precosat_add (int lit)
{
  int res;

  res = added_original_clauses;
  solver->add (lit);
  if (!lit) added_original_clauses++;

  return res;
}

int
btor_precosat_sat (int limit)
{
  int res;
  res = solver->solve (limit < 0 ? INT_MAX : limit);
  if (res < 0)
    res = 20;
  else if (res > 0)
    res = 10;
  else
    assert (!res);
  return res;
}

int
btor_precosat_deref (int lit)
{
  return solver->val (lit);
}

void
btor_precosat_reset (void)
{
  emgr                   = 0;
  new_for_precosat       = 0;
  delete_for_precosat    = 0;
  resize_for_precosat    = 0;
  added_original_clauses = 0;
  solver->reset ();
  delete solver;
  solver = 0;
}

void
btor_precosat_set_output (FILE *file)
{
  solver->set (file);
}

void
btor_precosat_set_prefix (const char *newprfx)
{
  solver->setprfx (newprfx);
}

int
btor_precosat_inc_max_var (void)
{
  return solver->next ();
}

int
btor_precosat_variables (void)
{
  return solver->getMaxVar ();
}

int
btor_precosat_added_original_clauses (void)
{
  return added_original_clauses;
}

void
btor_precosat_set_new (void *e, void *(n) (void *, size_t))
{
  assert (!emgr || emgr == e);
  assert (!new_for_precosat);
  emgr             = e;
  new_for_precosat = n;
}

void
btor_precosat_set_delete (void *e, void(d) (void *, void *, size_t))
{
  assert (!emgr || emgr == e);
  assert (!delete_for_precosat);
  emgr                = e;
  delete_for_precosat = d;
}

void
btor_precosat_set_resize (void *e, void *(r) (void *, void *, size_t, size_t))
{
  assert (!emgr || emgr == e);
  assert (!resize_for_precosat);
  emgr                = e;
  resize_for_precosat = r;
}

void
btor_precosat_stats (void)
{
  solver->prstats ();
}
};
#endif
