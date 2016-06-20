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
#include "utils/btorhashptr.h"
#include "utils/btoriter.h"
#include "utils/btorrng.h"

/*------------------------------------------------------------------------*/

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
    if (lname[j] == '-' || lname[j] == '_' || lname[j] == ':')
    {
      i -= 1;
      continue;
    }
    uname[i] = toupper ((int) lname[j]);
  }

  return getenv (uname);
}

static void
init_opt (Btor *btor,
          BtorOption opt,
          bool internal,
          bool isflag,
          char *lng,
          char *shrt,
          uint32_t val,
          uint32_t min,
          uint32_t max,
          char *desc)
{
  assert (btor);
  assert (opt >= 0 && opt < BTOR_OPT_NUM_OPTS);
  assert (lng);
  assert (max <= UINT_MAX);
  assert (min <= val);
  assert (val <= max);

  uint32_t v;
  char *valstr;

  assert (!btor_get_ptr_hash_table (btor->str2opt, lng));

  btor->options[opt].internal = internal;
  btor->options[opt].isflag   = isflag;
  btor->options[opt].shrt     = shrt;
  btor->options[opt].lng      = lng;
  btor->options[opt].val      = val;
  btor->options[opt].dflt     = val;
  btor->options[opt].min      = min;
  btor->options[opt].max      = max;
  btor->options[opt].desc     = desc;

  btor_add_ptr_hash_table (btor->str2opt, lng)->data.as_int = opt;

  if ((valstr = getenv_value (lng)))
  {
    v = atoi (valstr);
    if (v < min)
      v = min;
    else if (v > max)
      v = max;
    if (v == val) return;
    /* we need to trace options set via ENV vars */
    if (!internal)
      boolector_set_opt (btor, opt, v);
    else
      btor_set_opt (btor, opt, v);
  }
}

void
btor_init_opts (Btor *btor)
{
  assert (btor);

  BTOR_CNEWN (btor->mm, btor->options, BTOR_OPT_NUM_OPTS);
  btor->str2opt = btor_new_ptr_hash_table (
      btor->mm, (BtorHashPtr) btor_hash_str, (BtorCmpPtr) strcmp);

  init_opt (btor,
            BTOR_OPT_MODEL_GEN,
            false,
            true,
            "model-gen",
            "m",
            0,
            0,
            2,
            "print model for satisfiable instances");
  init_opt (btor,
            BTOR_OPT_INCREMENTAL,
            false,
            true,
            "incremental",
            "i",
            0,
            0,
            1,
            "incremental usage");
  init_opt (btor,
            BTOR_OPT_INCREMENTAL_ALL,
            false,
            true,
            "incremental-all",
            "I",
            0,
            0,
            1,
            "incremental, solve all (SMT1 only)");
  init_opt (btor,
            BTOR_OPT_INPUT_FORMAT,
            false,
            false,
            "input-format",
            0,
            BTOR_INPUT_FORMAT_DFLT,
            BTOR_INPUT_FORMAT_MIN,
            BTOR_INPUT_FORMAT_MAX,
            "input file format");
  init_opt (btor,
            BTOR_OPT_OUTPUT_NUMBER_FORMAT,
            false,
            false,
            "output-number-format",
            0,
            BTOR_OUTPUT_BASE_DFLT,
            BTOR_OUTPUT_BASE_MIN,
            BTOR_OUTPUT_BASE_MAX,
            "output number format");
  init_opt (btor,
            BTOR_OPT_OUTPUT_FORMAT,
            false,
            false,
            "output-format",
            0,
            BTOR_OUTPUT_FORMAT_DFLT,
            BTOR_OUTPUT_FORMAT_MIN,
            BTOR_OUTPUT_FORMAT_MAX,
            "output file format");
  init_opt (btor,
            BTOR_OPT_ENGINE,
            false,
            false,
            "engine",
            "E",
            BTOR_ENGINE_DFLT,
            BTOR_ENGINE_MIN,
            BTOR_ENGINE_MAX,
            "enable specific engine");
  init_opt (btor,
            BTOR_OPT_SAT_ENGINE,
            false,
            false,
            "sat-engine",
            "SE",
            BTOR_SAT_ENGINE_DFLT,
            BTOR_SAT_ENGINE_MIN + 1,
            BTOR_SAT_ENGINE_MAX - 1,
            "enable specific SAT solver");
  init_opt (btor,
            BTOR_OPT_AUTO_CLEANUP,
            false,
            true,
            "auto-cleanup",
            "ac",
            0,
            0,
            1,
            "auto cleanup on exit");
  init_opt (btor,
            BTOR_OPT_PRETTY_PRINT,
            false,
            true,
            "pretty-print",
            "p",
            1,
            0,
            1,
            "pretty print when dumping");
  init_opt (btor,
            BTOR_OPT_EXIT_CODES,
            false,
            true,
            "exit-codes",
            "e",
            1,
            0,
            1,
            "use Boolector exit codes");
  init_opt (btor,
            BTOR_OPT_SEED,
            false,
            false,
            "seed",
            "s",
            0,
            0,
            UINT_MAX,
            "random number generator seed");
  init_opt (btor,
            BTOR_OPT_VERBOSITY,
            false,
            true,
            "verbosity",
            "v",
            0,
            0,
            BTOR_VERBOSITY_MAX,
            "increase verbosity");
#ifndef NBTORLOG
  init_opt (btor,
            BTOR_OPT_LOGLEVEL,
            false,
            true,
            "loglevel",
            "l",
            0,
            0,
            UINT_MAX,
            "increase loglevel");
#endif

  /* simplifier --------------------------------------------------------- */
  init_opt (btor,
            BTOR_OPT_REWRITE_LEVEL,
            false,
            false,
            "rewrite-level",
            "rwl",
            3,
            0,
            3,
            "rewrite level");
  init_opt (btor,
            BTOR_OPT_SKELETON_PREPROC,
            false,
            true,
            "skeleton-preproc",
            "sp",
            1,
            0,
            1,
            "propositional skeleton preprocessing");
  init_opt (btor,
            BTOR_OPT_ACKERMANN,
            false,
            true,
            "ackermannize",
            "ack",
            0,
            0,
            1,
            "add ackermann constraints");
  init_opt (btor,
            BTOR_OPT_BETA_REDUCE_ALL,
            false,
            true,
            "beta-reduce-all",
            "bra",
            0,
            0,
            1,
            "eagerly eliminate lambda expressions");
  init_opt (btor,
            BTOR_OPT_ELIMINATE_SLICES,
            false,
            true,
            "eliminate-slices",
            "es",
            1,
            0,
            1,
            "eliminate slices on variables");
  init_opt (btor,
            BTOR_OPT_VAR_SUBST,
            false,
            true,
            "var-subst",
            "vs",
            1,
            0,
            1,
            "variable substitution");
  init_opt (btor,
            BTOR_OPT_UCOPT,
            false,
            true,
            "ucopt",
            "uc",
            0,
            0,
            1,
            "unconstrained optimization");
  init_opt (btor,
            BTOR_OPT_MERGE_LAMBDAS,
            false,
            true,
            "merge-lambdas",
            "ml",
            1,
            0,
            1,
            "merge lambda chains");
  init_opt (btor,
            BTOR_OPT_EXTRACT_LAMBDAS,
            false,
            true,
            "extract-lambdas",
            "xl",
            1,
            0,
            1,
            "extract lambda terms");

  /* FUN engine ---------------------------------------------------------- */
  init_opt (btor,
            BTOR_OPT_FUN_DUAL_PROP,
            false,
            true,
            "fun:dual-prop",
            "fun:dp",
            0,
            0,
            1,
            "dual propagation optimization");
  init_opt (btor,
            BTOR_OPT_FUN_JUST,
            false,
            true,
            "fun:just",
            "fun:ju",
            0,
            0,
            1,
            "justification optimization");
  init_opt (btor,
            BTOR_OPT_FUN_JUST_HEURISTIC,
            false,
            false,
            "fun:just-heuristic",
            0,
            BTOR_JUST_HEUR_DFLT,
            BTOR_JUST_HEUR_MIN,
            BTOR_JUST_HEUR_MAX,
            "justification heuristic");
  init_opt (btor,
            BTOR_OPT_FUN_LAZY_SYNTHESIZE,
            false,
            true,
            "fun:lazy-synthesize",
            "fun:ls",
            0,
            0,
            1,
            "lazily synthesize expressions");
  init_opt (btor,
            BTOR_OPT_FUN_EAGER_LEMMAS,
            false,
            true,
            "fun:eager-lemmas",
            "fun:el",
            1,
            0,
            1,
            "eager lemma generation");

  /* SLS engine ---------------------------------------------------------- */
  init_opt (btor,
            BTOR_OPT_SLS_STRATEGY,
            false,
            false,
            "sls:strategy",
            0,
            BTOR_SLS_STRAT_DFLT,
            BTOR_SLS_STRAT_MIN,
            BTOR_SLS_STRAT_MAX,
            "move strategy for sls");
  init_opt (btor,
            BTOR_OPT_SLS_JUST,
            false,
            true,
            "sls:just",
            0,
            0,
            0,
            1,
            "justification optimization");
  init_opt (btor,
            BTOR_OPT_SLS_MOVE_GW,
            false,
            true,
            "sls:move-gw",
            0,
            0,
            0,
            1,
            "select move by altering not only one "
            "but all candidate variables at once");
  init_opt (btor,
            BTOR_OPT_SLS_MOVE_RANGE,
            false,
            true,
            "sls:move-range",
            0,
            0,
            0,
            1,
            "try range-wise flips when selecting moves");
  init_opt (btor,
            BTOR_OPT_SLS_MOVE_SEGMENT,
            false,
            true,
            "sls:move-segment",
            0,
            0,
            0,
            1,
            "try segment-wise flips when selecting moves");
  init_opt (btor,
            BTOR_OPT_SLS_MOVE_RAND_WALK,
            false,
            true,
            "sls:move-rand-walk",
            0,
            0,
            0,
            1,
            "do a random walk (with given probability)");
  init_opt (btor,
            BTOR_OPT_SLS_MOVE_RAND_WALK_PROB,
            false,
            false,
            "sls:move-rand-walk-prob",
            0,
            100,
            0,
            BTOR_PROB_MAX,
            "probability for choosing random walks "
            "(interpreted as 1:<n>)");
  init_opt (btor,
            BTOR_OPT_SLS_MOVE_RAND_ALL,
            false,
            true,
            "sls:move-rand-all",
            0,
            0,
            0,
            1,
            "randomize all candidate variables (instead of only one) "
            "if no neighbor with better score is found");
  init_opt (btor,
            BTOR_OPT_SLS_MOVE_RAND_RANGE,
            false,
            true,
            "sls:move-rand-range",
            0,
            0,
            0,
            1,
            "randomize a range of bits of a randomly chosen candidate "
            "variable if neighbor with better score is found");

  init_opt (btor,
            BTOR_OPT_SLS_MOVE_PROP,
            false,
            true,
            "sls:move-prop",
            0,
            0,
            0,
            1,
            "enable propagation moves (with given ratio of propagation "
            "to regular moves)");
  init_opt (btor,
            BTOR_OPT_SLS_MOVE_PROP_N_PROP,
            false,
            false,
            "sls:move-prop-n-prop",
            0,
            1,
            0,
            UINT_MAX,
            "number of prop moves (moves are performed as <n>:m prop "
            "to sls moves");
  init_opt (btor,
            BTOR_OPT_SLS_MOVE_PROP_N_SLS,
            false,
            false,
            "sls:move-prop-n-sls",
            0,
            1,
            0,
            UINT_MAX,
            "number of sls moves (moves are performed as m:<n> prop "
            "to sls moves");
  init_opt (btor,
            BTOR_OPT_SLS_MOVE_PROP_FORCE_RW,
            false,
            true,
            "sls:move-prop-force-rw",
            0,
            0,
            0,
            1,
            "force random walk if propagation move fails");
  init_opt (btor,
            BTOR_OPT_SLS_MOVE_INC_MOVE_TEST,
            false,
            true,
            "sls:move-inc-move-test",
            0,
            0,
            0,
            1,
            "use prev. neighbor with better score as base for "
            "next move test");
  init_opt (btor,
            BTOR_OPT_SLS_USE_RESTARTS,
            false,
            true,
            "sls:use-restarts",
            0,
            1,
            0,
            1,
            "use restarts");
  init_opt (btor,
            BTOR_OPT_SLS_USE_BANDIT,
            false,
            true,
            "sls:use-bandit",
            0,
            1,
            0,
            1,
            "use bandit scheme for constraint selection");

  /* PROP engine ---------------------------------------------------------- */
  init_opt (btor,
            BTOR_OPT_PROP_USE_RESTARTS,
            false,
            true,
            "prop:use-restarts",
            0,
            0,
            0,
            1,
            "use restarts");
  init_opt (btor,
            BTOR_OPT_PROP_USE_BANDIT,
            false,
            true,
            "prop:use-bandit",
            0,
            0,
            0,
            1,
            "use bandit scheme for constraint selection");
  // TODO this is temporary for paper purposes only (eliminate)?
  init_opt (btor,
            BTOR_OPT_PROP_USE_FULL_PATH,
            false,
            true,
            "prop:use-full-path",
            0,
            1,
            0,
            1,
            "perform path selection over the full set of operators");
  init_opt (btor,
            BTOR_OPT_PROP_USE_INV_VALUE_PROB,
            false,
            false,
            "prop:use-inv-value-prob",
            0,
            990,
            0,
            BTOR_PROB_MAX,
            "probability for producing inverse rather than consistent values "
            "(interpreted as <n>%)");
  init_opt (btor,
            BTOR_OPT_PROP_FLIP_COND_PROB,
            false,
            false,
            "prop:flip-cond-prob",
            0,
            100,
            0,
            BTOR_PROB_MAX,
            "probability for choosing to flip the condition (rather than "
            "choosing the enabled path) for ITE during path selection "
            "for prop moves (interpreted as <n>%)");
  init_opt (btor,
            BTOR_OPT_PROP_NO_MOVE_ON_CONFLICT,
            false,
            true,
            "prop:no-move-on-conflict",
            0,
            0,
            0,
            1,
            "do not perform a propagation move when encountering a conflict"
            "during inverse computation");

  /* AIGPROP engine ------------------------------------------------------- */
  init_opt (btor,
            BTOR_OPT_AIGPROP_USE_RESTARTS,
            false,
            true,
            "aigprop:use-restarts",
            0,
            0,
            0,
            1,
            "use restarts");
  init_opt (btor,
            BTOR_OPT_AIGPROP_USE_BANDIT,
            false,
            true,
            "aigprop:use-bandit",
            0,
            0,
            0,
            1,
            "use bandit scheme for constraint selection");

  /* EF engine ----------------------------------------------------------- */
  init_opt (btor,
            BTOR_OPT_EF_MINISCOPING,
            false,
            true,
            "ef:miniscoping",
            "ef:ms",
            0,
            0,
            1,
            "miniscoping for EF solver");

  init_opt (btor,
            BTOR_OPT_EF_DUAL_PROP,
            false,
            true,
            "ef:dual-prop",
            "ef:dp",
            0,
            0,
            1,
            "dual propagation optimization for EF solver");
  init_opt (btor,
            BTOR_OPT_EF_DER,
            false,
            true,
            "ef:der",
            0,
            0,
            0,
            1,
            "destructive equality resolution for EF solver");
  init_opt (btor,
            BTOR_OPT_EF_CER,
            false,
            true,
            "ef:cer",
            0,
            0,
            0,
            1,
            "constructive equality resolution for EF solver");
  init_opt (btor,
            BTOR_OPT_EF_SYNTH,
            false,
            true,
            "ef:synth",
            0,
            1,
            0,
            1,
            "use synthesis for UF models");
  init_opt (btor,
            BTOR_OPT_EF_QINST_MODE,
            false,
            true,
            "ef:qinstmode",
            0,
            BTOR_EF_QINST_DEFAULT,
            BTOR_EF_QINST_MIN,
            BTOR_EF_QINST_MAX,
            "quantifier instantiation mode for refinment");
  init_opt (btor,
            BTOR_OPT_EF_DUAL_SOLVER,
            false,
            true,
            "ef:dual",
            0,
            0,
            0,
            1,
            "dual EF solver");

  /* internal options ---------------------------------------------------- */
  init_opt (btor,
            BTOR_OPT_SORT_EXP,
            true,
            true,
            "sort-exp",
            0,
            1,
            0,
            1,
            "sort commutative expression nodes");
  init_opt (btor,
            BTOR_OPT_SORT_AIG,
            true,
            true,
            "sort-aig",
            0,
            1,
            0,
            1,
            "sort AIG nodes");
  init_opt (btor,
            BTOR_OPT_SORT_AIGVEC,
            true,
            true,
            "sort-aigvec",
            0,
            1,
            0,
            1,
            "sort AIG vectors");
  init_opt (btor,
            BTOR_OPT_AUTO_CLEANUP_INTERNAL,
            true,
            true,
            "auto-cleanup-internal",
            0,
            0,
            0,
            1,
            0);
  init_opt (btor,
            BTOR_OPT_SIMPLIFY_CONSTRAINTS,
            true,
            true,
            "simplify-constraints",
            0,
            1,
            0,
            1,
            0);
#ifdef BTOR_CHECK_FAILED
  init_opt (btor,
            BTOR_OPT_CHK_FAILED_ASSUMPTIONS,
            true,
            true,
            "chk-failed-assumptions",
            0,
            1,
            0,
            1,
            0);
#endif
  init_opt (btor,
            BTOR_OPT_PARSE_INTERACTIVE,
            true,
            true,
            "parse-interactive",
            0,
            1,
            0,
            1,
            "interactive parse mode");
#ifdef BTOR_USE_LINGELING
  init_opt (btor,
            BTOR_OPT_SAT_ENGINE_LGL_FORK,
            true,
            true,
            "sat-engine-lgl-fork",
            0,
            1,
            0,
            1,
            "fork lingeling");
#endif
}

void
btor_clone_opts (Btor *btor, Btor *clone)
{
  assert (btor);

  BtorOption o;

  if (btor->options)
  {
    BTOR_CNEWN (clone->mm, clone->options, BTOR_OPT_NUM_OPTS);
    for (o = btor_first_opt (btor); btor_has_opt (btor, o);
         o = btor_next_opt (btor, o))
    {
      memcpy (&clone->options[o], &btor->options[o], sizeof (BtorOpt));
      if (btor->options[o].valstr)
        clone->options[o].valstr =
            btor_strdup (clone->mm, btor->options[o].valstr);
    }
  }
  if (btor->str2opt)
  {
    clone->str2opt = btor_clone_ptr_hash_table (clone->mm,
                                                btor->str2opt,
                                                btor_clone_key_as_static_str,
                                                btor_clone_data_as_int,
                                                0,
                                                0);
  }
}

void
btor_delete_opts (Btor *btor)
{
  assert (btor);

  BtorOption o;

  if (btor->options)
  {
    for (o = btor_first_opt (btor); btor_has_opt (btor, o);
         o = btor_next_opt (btor, o))
    {
      if (btor->options[o].valstr)
      {
        btor_freestr (btor->mm, btor->options[o].valstr);
        btor->options[o].valstr = 0;
      }
    }
    BTOR_DELETEN (btor->mm, btor->options, BTOR_OPT_NUM_OPTS);
    btor->options = 0;
  }
  if (btor->str2opt)
  {
    btor_delete_ptr_hash_table (btor->str2opt);
    btor->str2opt = 0;
  }
}

bool
btor_has_opt (Btor *btor, BtorOption opt)
{
  assert (btor);
  (void) btor;
  return opt >= 0 && opt < BTOR_OPT_NUM_OPTS;
}

uint32_t
btor_get_opt (Btor *btor, BtorOption opt)
{
  assert (btor);
  assert (btor_has_opt (btor, opt));

  return btor->options[opt].val;
}

uint32_t
btor_get_opt_min (Btor *btor, BtorOption opt)
{
  assert (btor);
  assert (btor_has_opt (btor, opt));

  return btor->options[opt].min;
}

uint32_t
btor_get_opt_max (Btor *btor, BtorOption opt)
{
  assert (btor);
  assert (btor_has_opt (btor, opt));

  return btor->options[opt].max;
}

uint32_t
btor_get_opt_dflt (Btor *btor, BtorOption opt)
{
  assert (btor);
  assert (btor_has_opt (btor, opt));

  return btor->options[opt].dflt;
}

const char *
btor_get_opt_lng (Btor *btor, BtorOption opt)
{
  assert (btor);
  assert (btor_has_opt (btor, opt));

  return (const char *) btor->options[opt].lng;
}

const char *
btor_get_opt_shrt (Btor *btor, BtorOption opt)
{
  assert (btor);
  assert (btor_has_opt (btor, opt));

  return (const char *) btor->options[opt].shrt;
}

const char *
btor_get_opt_desc (Btor *btor, BtorOption opt)
{
  assert (btor);
  assert (btor_has_opt (btor, opt));

  return (const char *) btor->options[opt].desc;
}

const char *
btor_get_opt_valstr (Btor *btor, BtorOption opt)
{
  assert (btor);
  assert (btor_has_opt (btor, opt));

  return (const char *) btor->options[opt].valstr;
}

void
btor_set_opt (Btor *btor, BtorOption opt, uint32_t val)
{
  assert (btor);
  assert (btor_has_opt (btor, opt));

  BtorOpt *o;

  o = &btor->options[opt];

#ifndef NDEBUG
  uint32_t oldval = o->val;
#endif

  if (val > o->max) val = o->max;
  if (val < o->min) val = o->min;
  o->val = val;

  if (opt == BTOR_OPT_SEED)
  {
    btor_init_rng (&btor->rng, val);
  }
  else if (opt == BTOR_OPT_ENGINE)
  {
    if (val == BTOR_ENGINE_SLS)
      btor_set_opt (btor, BTOR_OPT_PROP_NO_MOVE_ON_CONFLICT, 1);
    else if (val == BTOR_ENGINE_PROP)
      btor_set_opt (btor, BTOR_OPT_PROP_NO_MOVE_ON_CONFLICT, 0);
  }
  else if (opt == BTOR_OPT_MODEL_GEN)
  {
    if (!val && btor_get_opt (btor, opt)) btor_delete_model (btor);
    assert (!val || !btor_get_opt (btor, BTOR_OPT_UCOPT));
  }
  else if (opt == BTOR_OPT_UCOPT)
  {
    assert (!val || !btor_get_opt (btor, BTOR_OPT_MODEL_GEN));
    assert (!val || !btor_get_opt (btor, BTOR_OPT_INCREMENTAL));
  }
#ifndef NDEBUG
  else if (opt == BTOR_OPT_INCREMENTAL)
  {
    assert (btor->btor_sat_btor_called == 0);
  }
  else if (opt == BTOR_OPT_FUN_DUAL_PROP)
  {
    assert (!val || !btor_get_opt (btor, BTOR_OPT_FUN_JUST));
  }
  else if (opt == BTOR_OPT_FUN_JUST)
  {
    assert (!val || !btor_get_opt (btor, BTOR_OPT_FUN_DUAL_PROP));
  }
  else if (opt == BTOR_OPT_REWRITE_LEVEL)
  {
    assert (val <= 3);
    assert (oldval <= 3);
  }
#endif
}

void
btor_set_opt_str (Btor *btor, BtorOption opt, const char *str)
{
  assert (btor);
  assert (btor_has_opt (btor, opt));
  assert (opt == BTOR_OPT_SAT_ENGINE);

  btor->options[opt].valstr = btor_strdup (btor->mm, str);
}

BtorOption
btor_first_opt (Btor *btor)
{
  assert (btor);
  (void) btor;
  return (BtorOption) 0;
}

BtorOption
btor_next_opt (Btor *btor, BtorOption cur)
{
  assert (btor);
  assert (btor_has_opt (btor, cur));
  (void) btor;
  return (BtorOption) cur + 1;
}

#ifndef NBTORLOG
void
btor_log_opts (Btor *btor)
{
  assert (btor);

  BtorOption opt;

  for (opt = btor_first_opt (btor); btor_has_opt (btor, opt);
       opt = btor_next_opt (btor, opt))
    BTORLOG (2,
             "set option '%s' to %u",
             btor_get_opt_lng (btor, opt),
             btor_get_opt (btor, opt));
}
#endif
