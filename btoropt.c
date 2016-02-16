/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2014-2016 Aina Niemetz.
 *  Copyright (C) 2014-2015 Mathias Preiner.
 *  Copyright (C) 2015 Armin Biere.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btoropt.h"
#include <ctype.h>
#include <limits.h>
#include "boolector.h"
#include "btorclone.h"
#include "btorcore.h"
#include "btorlog.h"
#include "btormodel.h"
#include "btortrapi.h"
#include "utils/btorhashptr.h"
#include "utils/btoriter.h"

static char *
getenv_value (const char *lname)
{
  char uname[40];
  size_t i, j;

  assert (strlen (lname) + 4 + 1 < sizeof (uname));
  uname[0] = 'B';
  uname[1] = 'T';
  uname[2] = 'O';
  uname[3] = 'R';
  for (i = 4, j = 0; i < sizeof (uname); i++, j++)
  {
    if (lname[j] == '_')
    {
      i -= 1;
      continue;
    }
    uname[i] = toupper ((int) lname[j]);
  }

  return getenv (uname);
}

void
btor_init_opt (Btor *btor,
               bool internal,
               char *lng,
               char *shrt,
               uint32_t val,
               uint32_t min,
               uint32_t max,
               char *desc)
{
  assert (btor);
  assert (lng);
  assert (max <= UINT_MAX);
  assert (min <= val);
  assert (val <= max);

  BtorOpt *opt;
  uint32_t v;
  char *valstr;

  assert (!btor_get_ptr_hash_table (btor->options, lng));

  BTOR_CNEW (btor->mm, opt);
  opt->internal = internal;
  opt->shrt     = shrt;
  opt->lng      = lng;
  opt->val      = val;
  opt->dflt     = val;
  opt->min      = min;
  opt->max      = max;
  opt->desc     = desc;

  btor_add_ptr_hash_table (btor->options, lng)->data.as_ptr = opt;

  if ((valstr = getenv_value (lng)))
  {
    v = atoi (valstr);
    if (v < opt->min)
      v = opt->min;
    else if (v > opt->max)
      v = opt->max;
    if (v == val) return;
    /* we need to trace options set via ENV vars */
    if (!internal)
      boolector_set_opt (btor, lng, v);
    else
      btor_set_opt (btor, lng, v);
  }
}

void
btor_init_opts (Btor *btor)
{
  assert (btor);

  btor->options = btor_new_ptr_hash_table (
      btor->mm, (BtorHashPtr) btor_hash_str, (BtorCmpPtr) strcmp);

  btor_init_opt (btor,
                 false,
                 BTOR_OPT_MODEL_GEN,
                 "m",
                 0,
                 0,
                 2,
                 "print model for satisfiable instances");
  btor_init_opt (
      btor, false, BTOR_OPT_INCREMENTAL, "i", 0, 0, 1, "incremental usage");
  btor_init_opt (btor,
                 0,
                 BTOR_OPT_INCREMENTAL_ALL,
                 "I",
                 0,
                 0,
                 1,
                 "incremental, solve all (SMT1 only)");
  btor_init_opt (btor,
                 false,
                 BTOR_OPT_INPUT_FORMAT,
                 0,
                 BTOR_INPUT_FORMAT_DFLT,
                 BTOR_INPUT_FORMAT_MIN,
                 BTOR_INPUT_FORMAT_MAX,
                 "input file format");
  btor_init_opt (btor,
                 false,
                 BTOR_OPT_OUTPUT_NUMBER_FORMAT,
                 0,
                 BTOR_OUTPUT_BASE_DFLT,
                 BTOR_OUTPUT_BASE_MIN,
                 BTOR_OUTPUT_BASE_MAX,
                 "output number format");
  btor_init_opt (btor,
                 false,
                 BTOR_OPT_OUTPUT_FORMAT,
                 0,
                 BTOR_OUTPUT_FORMAT_DFLT,
                 BTOR_OUTPUT_FORMAT_MIN,
                 BTOR_OUTPUT_FORMAT_MAX,
                 "output file format");
  btor_init_opt (btor,
                 false,
                 BTOR_OPT_ENGINE,
                 "E",
                 BTOR_ENGINE_DFLT,
                 BTOR_ENGINE_MIN,
                 BTOR_ENGINE_MAX,
                 "enable specific engine");
  btor_init_opt (btor,
                 false,
                 BTOR_OPT_SAT_ENGINE,
                 "SE",
                 BTOR_SAT_ENGINE_DFLT,
                 BTOR_SAT_ENGINE_MIN + 1,
                 BTOR_SAT_ENGINE_MAX - 1,
                 "enable specific SAT solver");
  btor_init_opt (btor,
                 false,
                 BTOR_OPT_AUTO_CLEANUP,
                 "ac",
                 0,
                 0,
                 1,
                 "auto cleanup on exit");
  btor_init_opt (btor,
                 false,
                 BTOR_OPT_PRETTY_PRINT,
                 "p",
                 1,
                 0,
                 1,
                 "pretty print when dumping");
  btor_init_opt (btor,
                 false,
                 BTOR_OPT_EXIT_CODES,
                 "e",
                 1,
                 0,
                 1,
                 "use Boolector exit codes");
  btor_init_opt (btor,
                 false,
                 BTOR_OPT_SEED,
                 "s",
                 0,
                 0,
                 INT_MAX,
                 "random number generator seed");
  btor_init_opt (btor,
                 false,
                 BTOR_OPT_VERBOSITY,
                 "v",
                 0,
                 0,
                 BTOR_VERBOSITY_MAX,
                 "increase verbosity");
#ifndef NBTORLOG
  btor_init_opt (
      btor, false, BTOR_OPT_LOGLEVEL, "l", 0, 0, UINT_MAX, "increase loglevel");
#endif

  /* simplifier --------------------------------------------------------- */
  btor_init_opt (
      btor, false, BTOR_OPT_REWRITE_LEVEL, "rwl", 3, 0, 3, "rewrite level");
  btor_init_opt (btor,
                 false,
                 BTOR_OPT_SKELETON_PREPROC,
                 "sp",
                 1,
                 0,
                 1,
                 "propositional skeleton preprocessing");
  btor_init_opt (btor,
                 false,
                 BTOR_OPT_ACKERMANN,
                 "ack",
                 0,
                 0,
                 1,
                 "add ackermann constraints");
  btor_init_opt (btor,
                 false,
                 BTOR_OPT_BETA_REDUCE_ALL,
                 "bra",
                 0,
                 0,
                 1,
                 "eagerly eliminate lambda expressions");
  btor_init_opt (btor,
                 false,
                 BTOR_OPT_ELIMINATE_SLICES,
                 "es",
                 1,
                 0,
                 1,
                 "eliminate slices on variables");
  btor_init_opt (
      btor, false, BTOR_OPT_VAR_SUBST, "vs", 1, 0, 1, "variable substitution");
  btor_init_opt (
      btor, false, BTOR_OPT_UCOPT, "uc", 0, 0, 1, "unconstrained optimization");

  /* core engine -------------------------------------------------------- */
  btor_init_opt (btor,
                 false,
                 BTOR_OPT_DUAL_PROP,
                 "dp",
                 0,
                 0,
                 1,
                 "dual propagation optimization");
  btor_init_opt (btor,
                 false,
                 BTOR_OPT_JUST,
                 "just",
                 0,
                 0,
                 1,
                 "justification optimization");
  btor_init_opt (btor,
                 false,
                 BTOR_OPT_JUST_HEURISTIC,
                 0,
                 BTOR_JUST_HEUR_DFLT,
                 BTOR_JUST_HEUR_MIN,
                 BTOR_JUST_HEUR_MAX,
                 "justification heuristic");
  btor_init_opt (btor,
                 false,
                 BTOR_OPT_LAZY_SYNTHESIZE,
                 "ls",
                 0,
                 0,
                 1,
                 "lazily synthesize expressions");
  btor_init_opt (btor,
                 false,
                 BTOR_OPT_EAGER_LEMMAS,
                 "el",
                 1,
                 0,
                 1,
                 "eager lemma generation");
  btor_init_opt (btor,
                 false,
                 BTOR_OPT_MERGE_LAMBDAS,
                 "ml",
                 1,
                 0,
                 1,
                 "merge lambda chains");
  btor_init_opt (btor,
                 false,
                 BTOR_OPT_EXTRACT_LAMBDAS,
                 "xl",
                 1,
                 0,
                 1,
                 "extract lambda terms");

  /* SLS engine ---------------------------------------------------------- */
  btor_init_opt (btor,
                 false,
                 BTOR_OPT_SLS_STRATEGY,
                 0,
                 BTOR_SLS_STRAT_DFLT,
                 BTOR_SLS_STRAT_MIN,
                 BTOR_SLS_STRAT_MAX,
                 "move strategy for sls");
  btor_init_opt (
      btor, false, BTOR_OPT_SLS_JUST, 0, 0, 0, 1, "justification optimization");
  btor_init_opt (btor,
                 false,
                 BTOR_OPT_SLS_MOVE_GW,
                 0,
                 0,
                 0,
                 1,
                 "select move by altering not only one "
                 "but all candidate variables at once");
  btor_init_opt (btor,
                 false,
                 BTOR_OPT_SLS_MOVE_RANGE,
                 0,
                 0,
                 0,
                 1,
                 "try range-wise flips when selecting moves");
  btor_init_opt (btor,
                 false,
                 BTOR_OPT_SLS_MOVE_SEGMENT,
                 0,
                 0,
                 0,
                 1,
                 "try segment-wise flips when selecting moves");
  btor_init_opt (btor,
                 false,
                 BTOR_OPT_SLS_MOVE_RAND_WALK,
                 0,
                 0,
                 0,
                 1,
                 "do a random walk (with given probability)");
  btor_init_opt (btor,
                 false,
                 BTOR_OPT_SLS_MOVE_RAND_WALK_PROB,
                 0,
                 10,
                 0,
                 INT_MAX,
                 "probability for choosing random walks "
                 "(interpreted as 1:<n>)");
  btor_init_opt (btor,
                 false,
                 BTOR_OPT_SLS_MOVE_RAND_ALL,
                 0,
                 0,
                 0,
                 1,
                 "randomize all candidate variables (instead of only one) "
                 "if no neighbor with better score is found");
  btor_init_opt (btor,
                 false,
                 BTOR_OPT_SLS_MOVE_RAND_RANGE,
                 0,
                 0,
                 0,
                 1,
                 "randomize a range of bits of a randomly chosen candidate "
                 "variable if neighbor with better score is found");

  btor_init_opt (btor,
                 false,
                 BTOR_OPT_SLS_MOVE_PROP,
                 0,
                 0,
                 0,
                 1,
                 "enable propagation moves (with given ratio of propagation "
                 "to regular moves)");
  btor_init_opt (btor,
                 false,
                 BTOR_OPT_SLS_MOVE_PROP_N_PROP,
                 0,
                 1,
                 0,
                 UINT_MAX,
                 "number of prop moves (moves are performed as <n>:m prop "
                 "to sls moves");
  btor_init_opt (btor,
                 false,
                 BTOR_OPT_SLS_MOVE_PROP_N_SLS,
                 0,
                 1,
                 0,
                 UINT_MAX,
                 "number of sls moves (moves are performed as m:<n> prop "
                 "to sls moves");
  btor_init_opt (btor,
                 false,
                 BTOR_OPT_SLS_MOVE_PROP_NO_FLIP_COND,
                 0,
                 0,
                 0,
                 1,
                 "do not choose to flip the condition for ITE during "
                 "path selection");
  btor_init_opt (btor,
                 false,
                 BTOR_OPT_SLS_MOVE_PROP_FORCE_RW,
                 0,
                 0,
                 0,
                 1,
                 "force random walk if propagation move fails");
  btor_init_opt (btor,
                 false,
                 BTOR_OPT_SLS_MOVE_PROP_FLIP_COND_PROB,
                 0,
                 10,
                 0,
                 INT_MAX,
                 "probability for choosing to flip the condition (rather than "
                 "choosing the enabled path) for ITE during path selection "
                 "for prop moves (interpreted as 1:<n>)");
  btor_init_opt (btor,
                 false,
                 BTOR_OPT_SLS_MOVE_INC_MOVE_TEST,
                 0,
                 0,
                 0,
                 1,
                 "use prev. neighbor with better score as base for "
                 "next move test");

  btor_init_opt (
      btor, false, BTOR_OPT_SLS_USE_RESTARTS, 0, 1, 0, 1, "use restarts");
  btor_init_opt (btor,
                 false,
                 BTOR_OPT_SLS_USE_BANDIT,
                 0,
                 1,
                 0,
                 1,
                 "use bandit scheme for constraint selection");

  /* internal options ---------------------------------------------------- */
  btor_init_opt (btor,
                 false,
                 BTOR_OPT_SORT_EXP,
                 0,
                 1,
                 0,
                 1,
                 "sort commutative expression nodes");
  btor_init_opt (btor, false, BTOR_OPT_SORT_AIG, 0, 1, 0, 1, "sort AIG nodes");
  btor_init_opt (
      btor, false, BTOR_OPT_SORT_AIGVEC, 0, 1, 0, 1, "sort AIG vectors");
  btor_init_opt (btor, true, BTOR_OPT_AUTO_CLEANUP_INTERNAL, 0, 0, 0, 1, 0);
  btor_init_opt (btor, true, BTOR_OPT_SIMPLIFY_CONSTRAINTS, 0, 1, 0, 1, 0);
#ifdef BTOR_CHECK_FAILED
  btor_init_opt (btor, true, BTOR_OPT_CHK_FAILED_ASSUMPTIONS, 0, 1, 0, 1, 0);
#endif
  btor_init_opt (btor,
                 true,
                 BTOR_OPT_PARSE_INTERACTIVE,
                 0,
                 1,
                 0,
                 1,
                 "interactive parse mode");
  btor_init_opt (btor,
                 true,
                 BTOR_OPT_RW_NORMALIZE,
                 0,
                 1,
                 0,
                 1,
                 "normalize during rewriting");
#ifdef BTOR_USE_LINGELING
  btor_init_opt (
      btor, true, BTOR_OPT_SAT_ENGINE_LGL_FORK, 0, 1, 0, 1, "fork lingeling");
#endif
}

static void
clone_data_as_opt_ptr (BtorMemMgr *mm,
                       const void *map,
                       BtorPtrHashData *data,
                       BtorPtrHashData *cloned_data)
{
  assert (mm);
  assert (data);
  assert (cloned_data);

  (void) map;

  BtorOpt *opt, *cloned_opt;

  opt = (BtorOpt *) data->as_ptr;
  BTOR_NEW (mm, cloned_opt);
  memcpy (cloned_opt, opt, sizeof (BtorOpt));
  if (opt->valstr) cloned_opt->valstr = btor_strdup (mm, opt->valstr);
  cloned_data->as_ptr = cloned_opt;
}

BtorPtrHashTable *
btor_clone_opts (BtorMemMgr *mm, BtorPtrHashTable *options)
{
  assert (mm);
  assert (options);

  return btor_clone_ptr_hash_table (
      mm, options, btor_clone_key_as_static_str, clone_data_as_opt_ptr, 0, 0);
}

void
btor_delete_opts (Btor *btor)
{
  assert (btor);

  BtorOpt *o;
  BtorHashTableIterator it;

  if (!btor->options) return;

  btor_init_hash_table_iterator (&it, btor->options);
  while (btor_has_next_hash_table_iterator (&it))
  {
    o = (BtorOpt *) btor_next_data_hash_table_iterator (&it)->as_ptr;
    if (o->valstr)
    {
      btor_freestr (btor->mm, o->valstr);
      o->valstr = 0;
    }
    BTOR_DELETE (btor->mm, o);
  }
  btor_delete_ptr_hash_table (btor->options);
  btor->options = 0;
}

bool
btor_has_opt (Btor *btor, const char *name)
{
  assert (btor);
  assert (name);

  return btor_get_ptr_hash_table (btor->options, (void *) name) != 0;
}

uint32_t
btor_get_opt (Btor *btor, const char *name)
{
  assert (btor);
  assert (name);
  assert (btor_has_opt (btor, name));

  return ((BtorOpt *) btor_get_ptr_hash_table (btor->options, (void *) name)
              ->data.as_ptr)
      ->val;
}

uint32_t
btor_get_opt_min (Btor *btor, const char *name)
{
  assert (btor);
  assert (name);
  assert (btor_has_opt (btor, name));

  return ((BtorOpt *) btor_get_ptr_hash_table (btor->options, (void *) name)
              ->data.as_ptr)
      ->min;
}

uint32_t
btor_get_opt_max (Btor *btor, const char *name)
{
  assert (btor);
  assert (name);
  assert (btor_has_opt (btor, name));

  return ((BtorOpt *) btor_get_ptr_hash_table (btor->options, (void *) name)
              ->data.as_ptr)
      ->max;
}

uint32_t
btor_get_opt_dflt (Btor *btor, const char *name)
{
  assert (btor);
  assert (name);
  assert (btor_has_opt (btor, name));

  return ((BtorOpt *) btor_get_ptr_hash_table (btor->options, (void *) name)
              ->data.as_ptr)
      ->dflt;
}

const char *
btor_get_opt_shrt (Btor *btor, const char *name)
{
  assert (btor);
  assert (name);
  assert (btor_has_opt (btor, name));

  return (const char *) ((BtorOpt *) btor_get_ptr_hash_table (btor->options,
                                                              (void *) name)
                             ->data.as_ptr)
      ->shrt;
}

const char *
btor_get_opt_desc (Btor *btor, const char *name)
{
  assert (btor);
  assert (name);
  assert (btor_has_opt (btor, name));

  return (const char *) ((BtorOpt *) btor_get_ptr_hash_table (btor->options,
                                                              (void *) name)
                             ->data.as_ptr)
      ->desc;
}

const char *
btor_get_opt_valstr (Btor *btor, const char *name)
{
  assert (btor);
  assert (name);
  assert (btor_has_opt (btor, name));

  return (const char *) ((BtorOpt *) btor_get_ptr_hash_table (btor->options,
                                                              (void *) name)
                             ->data.as_ptr)
      ->valstr;
}

void
btor_set_opt (Btor *btor, const char *name, uint32_t val)
{
  assert (btor);
  assert (name);
  assert (btor_has_opt (btor, name));

  BtorOpt *opt;

  opt = (BtorOpt *) btor_get_ptr_hash_table (btor->options, (void *) name)
            ->data.as_ptr;

#ifndef NDEBUG
  uint32_t oldval = opt->val;
#endif

  if (val > opt->max) val = opt->max;
  if (val < opt->min) val = opt->min;
  opt->val = val;

  if (!strcmp (name, BTOR_OPT_MODEL_GEN))
  {
    if (!val && btor_get_opt (btor, name)) btor_delete_model (btor);
    assert (!val || !btor_get_opt (btor, BTOR_OPT_UCOPT));
  }
  else if (!strcmp (name, BTOR_OPT_UCOPT))
  {
    assert (!val || !btor_get_opt (btor, BTOR_OPT_MODEL_GEN));
    assert (!val || !btor_get_opt (btor, BTOR_OPT_INCREMENTAL));
  }
#ifndef NDEBUG
  else if (!strcmp (name, BTOR_OPT_INCREMENTAL))
  {
    assert (btor->btor_sat_btor_called == 0);
  }
  else if (!strcmp (name, BTOR_OPT_DUAL_PROP))
  {
    assert (!val || !btor_get_opt (btor, BTOR_OPT_JUST));
  }
  else if (!strcmp (name, BTOR_OPT_JUST))
  {
    assert (!val || !btor_get_opt (btor, BTOR_OPT_DUAL_PROP));
  }
  else if (!strcmp (name, BTOR_OPT_REWRITE_LEVEL))
  {
    assert (val <= 3);
    assert (oldval <= 3);
  }
#endif
}

void
btor_set_opt_str (Btor *btor, const char *name, const char *str)
{
  assert (btor);
  assert (name);
  assert (btor_has_opt (btor, name));
  assert (!strcmp (name, BTOR_OPT_SAT_ENGINE));

  BtorOpt *opt;

  opt = (BtorOpt *) btor_get_ptr_hash_table (btor->options, (void *) name)
            ->data.as_ptr;
  opt->valstr = btor_strdup (btor->mm, str);
}

const char *
btor_first_opt (Btor *btor)
{
  assert (btor);
  assert (btor->options->count);
  return (const char *) ((BtorOpt *) btor->options->first->data.as_ptr)->lng;
}

const char *
btor_next_opt (Btor *btor, const char *cur)
{
  assert (btor);
  assert (btor->options->count);
  assert (btor_has_opt (btor, cur));
  assert (cur);

  BtorPtrHashBucket *b;
  BtorOpt *opt;

  b = btor_get_ptr_hash_table (btor->options, (void *) cur);
  if (b == btor->options->last) return 0;
  b   = b->next;
  opt = (BtorOpt *) b->data.as_ptr;
  if (opt->internal) return 0;
  return (const char *) opt->lng;
}
