#include "boolector.h"
#include "btorexit.h"
#include "btorexp.h"

#define BTOR_ABORT_BOOLECTOR(cond, msg)        \
  do                                           \
  {                                            \
    if (cond)                                  \
    {                                          \
      fputs ("[boolector] " msg "\n", stdout); \
      exit (BTOR_ERR_EXIT);                    \
    }                                          \
  } while (0)

Btor*
boolector_new (void)
{
  return btor_new_btor ();
}

void
boolector_set_rewrite_level (Btor* btor, int rewrite_level)
{
  BTOR_ABORT_BOOLECTOR (
      btor == NULL, "'btor' must not be NULL in 'boolector_set_rewrite_level'");
  BTOR_ABORT_BOOLECTOR (
      rewrite_level < 0 || rewrite_level > 3,
      "'rewrite_level' has to be in [0,3] in 'boolector_set_rewrite_level'");
  BTOR_ABORT_BOOLECTOR (
      btor->id != 1,
      "setting rewrite level must be done before adding expressions");
  btor_set_rewrite_level_btor (btor, rewrite_level);
}

void
boolector_set_replay (Btor* btor, int replay)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL,
                        "'btor' must not be NULL in 'boolector_set_replay'");
  BTOR_ABORT_BOOLECTOR (
      btor->varsubst_constraints->count + btor->embedded_constraints->count
              + btor->unsynthesized_constraints->count
              + btor->synthesized_constraints->count + btor->assumptions->count
          > 0u,
      "setting replay must be done before add constraints and assumptions");
  btor_set_replay_btor (btor, replay);
}

void
boolector_set_verbosity (Btor* btor, int verbosity)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL,
                        "'btor' must not be NULL in 'boolector_set_verbosity'");
  BTOR_ABORT_BOOLECTOR (
      verbosity < -1 || verbosity > 3,
      "'verbosity' has to be in [-1,3] in 'boolector_set_verbosity'");
  BTOR_ABORT_BOOLECTOR (
      btor->id != 1,
      "'setting verbosity must be done before adding expressions'");
  btor_set_verbosity_btor (btor, verbosity);
}

void
boolector_delete (Btor* btor)
{
  BTOR_ABORT_BOOLECTOR (btor == NULL,
                        "'btor' must not be NULL in 'boolector_delete'");
  btor_delete_btor (btor);
}
