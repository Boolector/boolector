/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2014-2018 Aina Niemetz.
 *  Copyright (C) 2014-2017 Mathias Preiner.
 *  Copyright (C) 2015 Armin Biere.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btoropt.h"
#include <limits.h>
#include "boolector.h"
#include "btorclone.h"
#include "btorcore.h"
#include "btorlog.h"
#include "btormodel.h"
#include "btorparse.h"
#include "utils/btorhashptr.h"
#include "utils/btorrng.h"
#include "utils/btorutil.h"

/*------------------------------------------------------------------------*/

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
  assert (max <= UINT32_MAX);
  assert (min <= val);
  assert (val <= max);

  uint32_t v;
  char *valstr;

  assert (!btor_hashptr_table_get (btor->str2opt, lng));

  btor->options[opt].internal = internal;
  btor->options[opt].isflag   = isflag;
  btor->options[opt].shrt     = shrt;
  btor->options[opt].lng      = lng;
  btor->options[opt].val      = val;
  btor->options[opt].dflt     = val;
  btor->options[opt].min      = min;
  btor->options[opt].max      = max;
  btor->options[opt].desc     = desc;

  btor_hashptr_table_add (btor->str2opt, lng)->data.as_int = opt;

  if ((valstr = btor_util_getenv_value (btor->mm, lng)))
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
      btor_opt_set (btor, opt, v);
  }
}

void
btor_opt_init_opts (Btor *btor)
{
  assert (btor);

  BtorPtrHashTable *opts;

  BTOR_CNEWN (btor->mm, btor->options, BTOR_OPT_NUM_OPTS);
  btor->str2opt = btor_hashptr_table_new (
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
            BTOR_OPT_INCREMENTAL_SMT1,
            false,
            false,
            "incremental-smt1",
            "I",
            BTOR_PARSE_MODE_BASIC_INCREMENTAL,
            BTOR_PARSE_MODE_BASIC_INCREMENTAL,
            BTOR_PARSE_MODE_INCREMENTAL_BUT_CONTINUE,
            "incremental mode for SMT1");
  init_opt (btor,
            BTOR_OPT_INPUT_FORMAT,
            false,
            false,
            "input-format",
            0,
            BTOR_INPUT_FORMAT_DFLT,
            BTOR_INPUT_FORMAT_MIN + 1,
            BTOR_INPUT_FORMAT_MAX - 1,
            "input file format");
  opts = btor_hashptr_table_new (
      btor->mm, (BtorHashPtr) btor_hash_str, (BtorCmpPtr) strcmp);
  btor_hashptr_table_add (opts, "none")->data.as_int  = BTOR_INPUT_FORMAT_NONE;
  btor_hashptr_table_add (opts, "btor")->data.as_int  = BTOR_INPUT_FORMAT_BTOR;
  btor_hashptr_table_add (opts, "btor2")->data.as_int = BTOR_INPUT_FORMAT_BTOR2;
  btor_hashptr_table_add (opts, "smt1")->data.as_int  = BTOR_INPUT_FORMAT_SMT1;
  btor_hashptr_table_add (opts, "smt2")->data.as_int  = BTOR_INPUT_FORMAT_SMT2;
  btor->options[BTOR_OPT_INPUT_FORMAT].options        = opts;

  init_opt (btor,
            BTOR_OPT_OUTPUT_NUMBER_FORMAT,
            false,
            false,
            "output-number-format",
            0,
            BTOR_OUTPUT_BASE_DFLT,
            BTOR_OUTPUT_BASE_MIN + 1,
            BTOR_OUTPUT_BASE_MAX - 1,
            "output number format");
  opts = btor_hashptr_table_new (
      btor->mm, (BtorHashPtr) btor_hash_str, (BtorCmpPtr) strcmp);
  btor_hashptr_table_add (opts, "bin")->data.as_int    = BTOR_OUTPUT_BASE_BIN;
  btor_hashptr_table_add (opts, "hex")->data.as_int    = BTOR_OUTPUT_BASE_HEX;
  btor_hashptr_table_add (opts, "dec")->data.as_int    = BTOR_OUTPUT_BASE_DEC;
  btor->options[BTOR_OPT_OUTPUT_NUMBER_FORMAT].options = opts;

  init_opt (btor,
            BTOR_OPT_OUTPUT_FORMAT,
            false,
            false,
            "output-format",
            0,
            BTOR_OUTPUT_FORMAT_DFLT,
            BTOR_OUTPUT_FORMAT_MIN + 1,
            BTOR_OUTPUT_FORMAT_MAX - 1,
            "output file format");
  opts = btor_hashptr_table_new (
      btor->mm, (BtorHashPtr) btor_hash_str, (BtorCmpPtr) strcmp);
  btor_hashptr_table_add (opts, "btor")->data.as_int =
      BTOR_OUTPUT_FORMAT_BTOR;
  btor_hashptr_table_add (opts, "btor2")->data.as_int =
      BTOR_OUTPUT_FORMAT_BTOR2;
  btor_hashptr_table_add (opts, "smt2")->data.as_int =
      BTOR_OUTPUT_FORMAT_SMT2;
  btor_hashptr_table_add (opts, "aiger")->data.as_int =
      BTOR_OUTPUT_FORMAT_AIGER_ASCII;
  btor_hashptr_table_add (opts, "aigerbin")->data.as_int =
      BTOR_OUTPUT_FORMAT_AIGER_BINARY;
  btor->options[BTOR_OPT_OUTPUT_FORMAT].options = opts;

  init_opt (btor,
            BTOR_OPT_ENGINE,
            false,
            false,
            "engine",
            "E",
            BTOR_ENGINE_DFLT,
            BTOR_ENGINE_MIN + 1,
            BTOR_ENGINE_MAX - 1,
            "enable specific engine");
  opts = btor_hashptr_table_new (
      btor->mm, (BtorHashPtr) btor_hash_str, (BtorCmpPtr) strcmp);
  btor_hashptr_table_add (opts, "fun")->data.as_int     = BTOR_ENGINE_FUN;
  btor_hashptr_table_add (opts, "sls")->data.as_int     = BTOR_ENGINE_SLS;
  btor_hashptr_table_add (opts, "prop")->data.as_int    = BTOR_ENGINE_PROP;
  btor_hashptr_table_add (opts, "aigprop")->data.as_int = BTOR_ENGINE_AIGPROP;
  btor_hashptr_table_add (opts, "quant")->data.as_int   = BTOR_ENGINE_QUANT;
  btor->options[BTOR_OPT_ENGINE].options = opts;


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
  opts = btor_hashptr_table_new (
      btor->mm, (BtorHashPtr) btor_hash_str, (BtorCmpPtr) strcmp);
  btor_hashptr_table_add (opts, "lingeling")->data.as_int =
      BTOR_SAT_ENGINE_LINGELING;
  btor_hashptr_table_add (opts, "picosat")->data.as_int =
      BTOR_SAT_ENGINE_PICOSAT;
  btor_hashptr_table_add (opts, "minisat")->data.as_int =
      BTOR_SAT_ENGINE_MINISAT;
  btor_hashptr_table_add (opts, "cadical")->data.as_int =
      BTOR_SAT_ENGINE_CADICAL;
  btor->options[BTOR_OPT_SAT_ENGINE].options = opts;

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
            UINT32_MAX,
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
  init_opt (btor,
            BTOR_OPT_LOGLEVEL,
            false,
            true,
            "loglevel",
            "l",
            0,
            0,
            UINT32_MAX,
            "increase loglevel");

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
  init_opt (btor,
            BTOR_OPT_NORMALIZE_ADD,
            false,
            true,
            "normalize-add",
            "nadd",
            1,
            0,
            1,
            "normalize addition operators");
  init_opt (btor,
            BTOR_OPT_NORMALIZE,
            false,
            true,
            "normalize",
            "norm",
            1,
            0,
            1,
            "normalize add/mul/and operators");

  /* FUN engine ---------------------------------------------------------- */
  init_opt (btor,
            BTOR_OPT_FUN_PREPROP,
            false,
            true,
            "fun:preprop",
            0,
            0,
            0,
            1,
            "run prop engine as a preprocessing step "
            "within a sequential portfolio "
            "(QF_BV only!)");
  init_opt (btor,
            BTOR_OPT_FUN_PRESLS,
            false,
            true,
            "fun:presls",
            0,
            0,
            0,
            1,
            "run sls engine as a preprocessing step "
            "within a sequential portfolio "
            "(QF_BV only!)");
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
            BTOR_OPT_FUN_DUAL_PROP_QSORT,
            false,
            false,
            "fun:dual-prop-qsort",
            0,
            BTOR_DP_QSORT_DFLT,
            BTOR_DP_QSORT_MIN + 1,
            BTOR_DP_QSORT_MAX - 1,
            "order in which to assume inputs in dual solver");
  opts = btor_hashptr_table_new (
      btor->mm, (BtorHashPtr) btor_hash_str, (BtorCmpPtr) strcmp);
  btor_hashptr_table_add (opts, "just")->data.as_int  = BTOR_DP_QSORT_JUST;
  btor_hashptr_table_add (opts, "asc")->data.as_int   = BTOR_DP_QSORT_ASC;
  btor_hashptr_table_add (opts, "desc")->data.as_int  = BTOR_DP_QSORT_DESC;
  btor->options[BTOR_OPT_FUN_DUAL_PROP_QSORT].options = opts;

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
            BTOR_JUST_HEUR_MIN + 1,
            BTOR_JUST_HEUR_MAX - 1,
            "justification heuristic");
  opts = btor_hashptr_table_new (
      btor->mm, (BtorHashPtr) btor_hash_str, (BtorCmpPtr) strcmp);
  btor_hashptr_table_add (opts, "left")->data.as_int =
      BTOR_JUST_HEUR_LEFT;
  btor_hashptr_table_add (opts, "app")->data.as_int =
      BTOR_JUST_HEUR_BRANCH_MIN_APP;
  btor_hashptr_table_add (opts, "dep")->data.as_int =
      BTOR_JUST_HEUR_BRANCH_MIN_DEP;
  btor->options[BTOR_OPT_FUN_JUST_HEURISTIC].options = opts;

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
            false,
            "fun:eager-lemmas",
            "fun:el",
            BTOR_FUN_EAGER_LEMMAS_DFLT,
            BTOR_FUN_EAGER_LEMMAS_MIN + 1,
            BTOR_FUN_EAGER_LEMMAS_MAX - 1,
            "eager lemma generation");
  opts = btor_hashptr_table_new (
      btor->mm, (BtorHashPtr) btor_hash_str, (BtorCmpPtr) strcmp);
  btor_hashptr_table_add (opts, "none")->data.as_int =
      BTOR_FUN_EAGER_LEMMAS_NONE;
  btor_hashptr_table_add (opts, "conf")->data.as_int =
      BTOR_FUN_EAGER_LEMMAS_CONF;
  btor_hashptr_table_add (opts, "all")->data.as_int = BTOR_FUN_EAGER_LEMMAS_ALL;
  btor->options[BTOR_OPT_FUN_EAGER_LEMMAS].options  = opts;

  init_opt (btor,
            BTOR_OPT_FUN_STORE_LAMBDAS,
            false,
            true,
            "fun:store-lambdas",
            "fun:sl",
            0,
            0,
            1,
            "represent array store as lambda");

  /* SLS engine ---------------------------------------------------------- */
  init_opt (btor,
            BTOR_OPT_SLS_NFLIPS,
            false,
            false,
            "sls:nflips",
            0,
            0,
            0,
            UINT32_MAX,
            "number of bit-flips used as a limit for sls engine");

  init_opt (btor,
            BTOR_OPT_SLS_STRATEGY,
            false,
            false,
            "sls:strategy",
            0,
            BTOR_SLS_STRAT_DFLT,
            BTOR_SLS_STRAT_MIN + 1,
            BTOR_SLS_STRAT_MAX - 1,
            "move strategy for sls");
  opts = btor_hashptr_table_new (
      btor->mm, (BtorHashPtr) btor_hash_str, (BtorCmpPtr) strcmp);
  btor_hashptr_table_add (opts, "best")->data.as_int = BTOR_SLS_STRAT_BEST_MOVE;
  btor_hashptr_table_add (opts, "walk")->data.as_int = BTOR_SLS_STRAT_RAND_WALK;
  btor_hashptr_table_add (opts, "first")->data.as_int = BTOR_SLS_STRAT_FIRST_BEST_MOVE;
  btor_hashptr_table_add (opts, "same")->data.as_int = BTOR_SLS_STRAT_BEST_SAME_MOVE;
  btor_hashptr_table_add (opts, "prop")->data.as_int = BTOR_SLS_STRAT_BEST_SAME_MOVE;
  btor->options[BTOR_OPT_SLS_STRATEGY].options = opts;

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
            BTOR_OPT_SLS_PROB_MOVE_RAND_WALK,
            false,
            false,
            "sls:prob-move-rand-walk",
            0,
            100,
            0,
            BTOR_PROB_MAX,
            "probability for choosing random walks "
            "(interpreted as <n>/1000)");
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
            UINT32_MAX,
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
            UINT32_MAX,
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
            BTOR_OPT_PROP_NPROPS,
            false,
            false,
            "prop:nprops",
            0,
            0,
            0,
            UINT32_MAX,
            "number of propagation steps used as a limit for prop engine");
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

  init_opt (btor,
            BTOR_OPT_PROP_PATH_SEL,
            false,
            false,
            "prop:path-sel",
            0,
            BTOR_PROP_PATH_SEL_DFLT,
            BTOR_PROP_PATH_SEL_MIN + 1,
            BTOR_PROP_PATH_SEL_MAX - 1,
            "path selection mode");
  opts = btor_hashptr_table_new (
      btor->mm, (BtorHashPtr) btor_hash_str, (BtorCmpPtr) strcmp);
  btor_hashptr_table_add (opts, "controlling")->data.as_int =
      BTOR_PROP_PATH_SEL_CONTROLLING;
  btor_hashptr_table_add (opts, "essential")->data.as_int =
      BTOR_PROP_PATH_SEL_ESSENTIAL;
  btor_hashptr_table_add (opts, "random")->data.as_int =
      BTOR_PROP_PATH_SEL_RANDOM;
  btor->options[BTOR_OPT_PROP_PATH_SEL].options = opts;

  init_opt (btor,
            BTOR_OPT_PROP_PROB_USE_INV_VALUE,
            false,
            false,
            "prop:prob-use-inv-value",
            0,
            990,
            0,
            BTOR_PROB_MAX,
            "probability for producing inverse rather than consistent values "
            "(interpreted as <n>/1000)");
  init_opt (btor,
            BTOR_OPT_PROP_PROB_FLIP_COND,
            false,
            false,
            "prop:prob-flip-cond",
            0,
            100,
            0,
            BTOR_PROB_MAX,
            "probability for choosing to flip the condition (rather than "
            "choosing the enabled path) for ITE during path selection "
            "for prop moves (interpreted as <n>/1000)");
  init_opt (btor,
            BTOR_OPT_PROP_PROB_FLIP_COND_CONST,
            false,
            false,
            "prop:prob-flip-cond-const",
            0,
            100,
            0,
            BTOR_PROB_MAX,
            "probability for choosing to flip the condition (rather than "
            "choosing the enabled path) for ITE during path selection "
            "for prop moves if either of the 'then' or 'else' branches "
            "is constant (interpreted as <n>/1000)");
  init_opt (btor,
            BTOR_OPT_PROP_FLIP_COND_CONST_NPATHSEL,
            false,
            false,
            "prop:flip-cond-const-npathsel",
            0,
            500,
            0,
            INT32_MAX,
            "limit for how often to flip the condition (rather than choosing "
            "the enabled branch) for ITE during path selection before "
            "decreasing or increasing the probability for flipping the "
            "condition if either the 'then' or 'else' branch is constant");
  init_opt (btor,
            BTOR_OPT_PROP_FLIP_COND_CONST_DELTA,
            false,
            false,
            "prop:flip-cond-const-delta",
            0,
            100,
            0,
            INT32_MAX,
            "delta by which the limit for how often to flip the condition "
            "(rather than choosing the enabled branch) for ITE during path "
            "is decreased or increased");
  init_opt (btor,
            BTOR_OPT_PROP_PROB_SLICE_KEEP_DC,
            false,
            false,
            "prop:prob-slice-keep-dc",
            0,
            500,
            0,
            BTOR_PROB_MAX,
            "probability for keeping the current value of the don't care "
            "bits of the operand of a slice operation "
            "(rather than fully randomizing all of them, "
            "for both inverse and consistent value selection) "
            "if their current value is not kept "
            "(interpreted as <n>/1000)");
  init_opt (btor,
            BTOR_OPT_PROP_PROB_CONC_FLIP,
            false,
            false,
            "prop:prob-conc-flip",
            0,
            900,
            0,
            BTOR_PROB_MAX,
            "probability for using slice of current assignment with max. "
            "one of its bits flipped (rather than using slice of down "
            "propagated assignment) as result of consistent value selction "
            "for concats (interpreted as <n>/1000)");
  init_opt (btor,
            BTOR_OPT_PROP_PROB_SLICE_FLIP,
            false,
            false,
            "prop:prob-slice-flip",
            0,
            0,
            0,
            BTOR_PROB_MAX,
            "probability for using the current assignment of the operand "
            "of a slice operation with max. one of its bits flipped "
            "(rather than fully randomizing all of them) as a result of "
            "inverse/consistent value selection "
            "(interpreted as <n>/1000)");
  init_opt (btor,
            BTOR_OPT_PROP_PROB_EQ_FLIP,
            false,
            false,
            "prop:prob-eq-flip",
            0,
            0,
            0,
            BTOR_PROB_MAX,
            "probability for using the current assignment of the selected "
            "node with one of its bits flipped (rather than using a fully "
            "randomized node) in case of inequalities "
            "(for both inverse and consistent value selection) "
            "(interpreted as <n>/1000)");
  init_opt (
      btor,
      BTOR_OPT_PROP_PROB_AND_FLIP,
      false,
      false,
      "prop:prob-and-flip",
      0,
      0,
      0,
      BTOR_PROB_MAX,
      "probability for using the current assignment of the don't care "
      "bits of the selected node with max. one of its bits flipped "
      "(rather fully randomizing all of them) in case of an and operation "
      "(for both inverse and consistent value selection) "
      "(interpreted as <n>/1000)");
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

  /* QUANT engine ----------------------------------------------------------- */
  init_opt (btor,
            BTOR_OPT_QUANT_DER,
            false,
            true,
            "quant:der",
            0,
            1,
            0,
            1,
            "apply destructive equality resolution (DER)");
  init_opt (btor,
            BTOR_OPT_QUANT_CER,
            false,
            true,
            "quant:cer",
            0,
            1,
            0,
            1,
            "apply constructive equality resolution (CER)");
  init_opt (btor,
            BTOR_OPT_QUANT_MINISCOPE,
            false,
            true,
            "quant:ms",
            0,
            1,
            0,
            1,
            "apply miniscoping");

  init_opt (btor,
            BTOR_OPT_QUANT_SYNTH,
            false,
            true,
            "quant:synth",
            0,
            BTOR_QUANT_SYNTH_DFLT,
            BTOR_QUANT_SYNTH_MIN,
            BTOR_QUANT_SYNTH_MAX,
            "synthesis mode for Skolem functions:"
            "0=none,"
            "1=enumlearn,"
            "2=enumlearn modulo predicates,"
            "3=1+2 combined,"
            "4=enumlearn modulo formula");
  opts = btor_hashptr_table_new (
      btor->mm, (BtorHashPtr) btor_hash_str, (BtorCmpPtr) strcmp);
  btor_hashptr_table_add (opts, "none")->data.as_int = BTOR_QUANT_SYNTH_NONE;
  btor_hashptr_table_add (opts, "el")->data.as_int   = BTOR_QUANT_SYNTH_EL;
  btor_hashptr_table_add (opts, "elmc")->data.as_int = BTOR_QUANT_SYNTH_ELMC;
  btor_hashptr_table_add (opts, "elelmc")->data.as_int =
      BTOR_QUANT_SYNTH_EL_ELMC;
  btor_hashptr_table_add (opts, "elmr")->data.as_int = BTOR_QUANT_SYNTH_ELMR;
  btor->options[BTOR_OPT_QUANT_SYNTH].options        = opts;

  init_opt (btor,
            BTOR_OPT_QUANT_DUAL_SOLVER,
            false,
            true,
            "quant:dual",
            0,
            1,
            0,
            1,
            "dual solver");
  init_opt (btor,
            BTOR_OPT_QUANT_SYNTH_LIMIT,
            false,
            false,
            "quant:synthlimit",
            0,
            10000,
            0,
            UINT32_MAX,
            "number of checks for synthesizing terms");
  init_opt (btor,
            BTOR_OPT_QUANT_SYNTH_ITE_COMPLETE,
            false,
            true,
            "quant:synthcomplete",
            0,
            1,
            0,
            1,
            "make base case of concrete model constant instead of undef.");
  init_opt (btor,
            BTOR_OPT_QUANT_FIXSYNTH,
            false,
            true,
            "quant:fixsynth",
            0,
            1,
            0,
            1,
            "update current model w.r.t. synthesized skolem function");
  init_opt (btor,
            BTOR_OPT_QUANT_SYNTH_QI,
            false,
            true,
            "quant:synthqi",
            0,
            1,
            0,
            1,
            "synthesize quantifier instantiations from counterexamples");

  /* internal options ---------------------------------------------------- */
  init_opt (btor,
            BTOR_OPT_DEFAULT_TO_CADICAL,
            true,
            true,
            "default-cadical",
            0,
            0,
            0,
            1,
            "default to CaDiCaL for non-incremental QF_BV");
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
  init_opt (btor, BTOR_OPT_CHK_MODEL, true, true, "chk-model", 0, 1, 0, 1, 0);
  init_opt (btor,
            BTOR_OPT_CHK_UNCONSTRAINED,
            true,
            true,
            "chk-unconstrained",
            0,
            1,
            0,
            1,
            0);
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
  init_opt (btor,
            BTOR_OPT_INCREMENTAL_RW,
            true,
            true,
            "incremental-rw",
            0,
            0,
            0,
            1,
            "enable simplifications that rewrite already synthesized nodes "
            "in incremental mode");
  init_opt (btor,
            BTOR_OPT_DECLSORT_BV_WIDTH,
            true,
            false,
            "declsort-bv-width",
            0,
            0,
            0,
            UINT32_MAX,
            "interpret sorts introduced with declare-sort as bit-vectors of "
            "given width");
}

void
btor_opt_clone_opts (Btor *btor, Btor *clone)
{
  assert (btor);

  BtorOption o;

  if (btor->options)
  {
    BTOR_CNEWN (clone->mm, clone->options, BTOR_OPT_NUM_OPTS);
    for (o = btor_opt_first (btor); btor_opt_is_valid (btor, o);
         o = btor_opt_next (btor, o))
    {
      memcpy (&clone->options[o], &btor->options[o], sizeof (BtorOpt));
      if (btor->options[o].valstr)
        clone->options[o].valstr =
            btor_mem_strdup (clone->mm, btor->options[o].valstr);
      if (btor->options[o].options)
        clone->options[o].options =
            btor_hashptr_table_clone (clone->mm,
                                      btor->options[o].options,
                                      btor_clone_key_as_static_str,
                                      btor_clone_data_as_int,
                                      0,
                                      0);
    }
  }
  if (btor->str2opt)
  {
    clone->str2opt = btor_hashptr_table_clone (clone->mm,
                                               btor->str2opt,
                                               btor_clone_key_as_static_str,
                                               btor_clone_data_as_int,
                                               0,
                                               0);
  }
}

void
btor_opt_delete_opts (Btor *btor)
{
  assert (btor);

  BtorOption o;

  if (btor->options)
  {
    for (o = btor_opt_first (btor); btor_opt_is_valid (btor, o);
         o = btor_opt_next (btor, o))
    {
      if (btor->options[o].valstr)
      {
        btor_mem_freestr (btor->mm, btor->options[o].valstr);
        btor->options[o].valstr = 0;
      }
      if (btor->options[o].options)
        btor_hashptr_table_delete (btor->options[o].options);
    }
    BTOR_DELETEN (btor->mm, btor->options, BTOR_OPT_NUM_OPTS);
    btor->options = 0;
  }
  if (btor->str2opt)
  {
    btor_hashptr_table_delete (btor->str2opt);
    btor->str2opt = 0;
  }
}

bool
btor_opt_is_valid (Btor *btor, const BtorOption opt)
{
  assert (btor);
  (void) btor;
  return opt < BTOR_OPT_NUM_OPTS;
}

uint32_t
btor_opt_get (Btor *btor, const BtorOption opt)
{
  assert (btor);
  assert (btor_opt_is_valid (btor, opt));

  return btor->options[opt].val;
}

uint32_t
btor_opt_get_min (Btor *btor, const BtorOption opt)
{
  assert (btor);
  assert (btor_opt_is_valid (btor, opt));

  return btor->options[opt].min;
}

uint32_t
btor_opt_get_max (Btor *btor, const BtorOption opt)
{
  assert (btor);
  assert (btor_opt_is_valid (btor, opt));

  return btor->options[opt].max;
}

uint32_t
btor_opt_get_dflt (Btor *btor, const BtorOption opt)
{
  assert (btor);
  assert (btor_opt_is_valid (btor, opt));

  return btor->options[opt].dflt;
}

const char *
btor_opt_get_lng (Btor *btor, const BtorOption opt)
{
  assert (btor);
  assert (btor_opt_is_valid (btor, opt));

  return (const char *) btor->options[opt].lng;
}

const char *
btor_opt_get_shrt (Btor *btor, const BtorOption opt)
{
  assert (btor);
  assert (btor_opt_is_valid (btor, opt));

  return (const char *) btor->options[opt].shrt;
}

const char *
btor_opt_get_desc (Btor *btor, const BtorOption opt)
{
  assert (btor);
  assert (btor_opt_is_valid (btor, opt));

  return (const char *) btor->options[opt].desc;
}

const char *
btor_opt_get_valstr (Btor *btor, const BtorOption opt)
{
  assert (btor);
  assert (btor_opt_is_valid (btor, opt));

  return (const char *) btor->options[opt].valstr;
}

void
btor_opt_set (Btor *btor, const BtorOption opt, uint32_t val)
{
  assert (btor);
  assert (btor_opt_is_valid (btor, opt));

  BtorOpt *o;
  uint32_t oldval;

  o      = &btor->options[opt];
  oldval = o->val;
  (void) oldval;

  if (opt == BTOR_OPT_SEED)
  {
    btor_rng_init (&btor->rng, val);
  }
  else if (opt == BTOR_OPT_ENGINE)
  {
    if (val == BTOR_ENGINE_SLS)
      btor_opt_set (btor, BTOR_OPT_PROP_NO_MOVE_ON_CONFLICT, 1);
    else if (val == BTOR_ENGINE_PROP)
      btor_opt_set (btor, BTOR_OPT_PROP_NO_MOVE_ON_CONFLICT, 0);
  }
  else if (opt == BTOR_OPT_MODEL_GEN)
  {
    if (!val && btor_opt_get (btor, opt)) btor_model_delete (btor);
    if (val && btor_opt_get (btor, BTOR_OPT_UCOPT))
    {
      btor_opt_set (btor, BTOR_OPT_UCOPT, 0);
      BTOR_MSG (btor->msg,
                1,
                "Disabling unconstrained optimization since model generation "
                "is enabled");
    }
    assert (!val || !btor_opt_get (btor, BTOR_OPT_UCOPT));
  }
  else if (opt == BTOR_OPT_UCOPT)
  {
    if (val && btor_opt_get (btor, BTOR_OPT_MODEL_GEN))
    {
      BTOR_MSG (btor->msg,
                1,
                "Disabling unconstrained optimization since model generation "
                "is enabled");
      val = 0;
    }
    assert (!val || !btor_opt_get (btor, BTOR_OPT_INCREMENTAL));
  }
  else if (opt == BTOR_OPT_SAT_ENGINE)
  {
#ifndef BTOR_USE_LINGELING
    if (val == BTOR_SAT_ENGINE_LINGELING)
    {
      val = oldval;
      BTOR_MSG (
          btor->msg,
          1,
          "SAT solver Lingeling not compiled in, using %s",
          oldval == BTOR_SAT_ENGINE_CADICAL
              ? "Cadical"
              : (oldval == BTOR_SAT_ENGINE_MINISAT ? "MiniSat" : "PicoSat"));
    }
#endif
#ifndef BTOR_USE_CADICAL
    if (val == BTOR_SAT_ENGINE_CADICAL)
    {
      val = oldval;
      BTOR_MSG (
          btor->msg,
          1,
          "SAT solver Cadical not compiled in, using %s",
          oldval == BTOR_SAT_ENGINE_LINGELING
              ? "Lingeling"
              : (oldval == BTOR_SAT_ENGINE_MINISAT ? "MiniSat" : "PicoSat"));
    }
#endif
#ifndef BTOR_USE_MINISAT
    if (val == BTOR_SAT_ENGINE_MINISAT)
    {
      val = oldval;
      BTOR_MSG (btor->msg,
                1,
                "SAT solver Minisat not compiled in, using %s",
                oldval == BTOR_SAT_ENGINE_CADICAL
                    ? "Cadical"
                    : (oldval == BTOR_SAT_ENGINE_LINGELING ? "Lingeling"
                                                           : "PicoSat"));
    }
#endif
#ifndef BTOR_USE_PICOSAT
    if (val == BTOR_SAT_ENGINE_PICOSAT)
    {
      val = oldval;
      BTOR_MSG (btor->msg,
                1,
                "SAT solver Picosat not compiled in, using %s",
                oldval == BTOR_SAT_ENGINE_CADICAL
                    ? "Cadical"
                    : (oldval == BTOR_SAT_ENGINE_LINGELING ? "Lingeling"
                                                           : "MiniSat"));
    }
#endif
  }
#ifndef BTOR_USE_LINGELING
  else if (opt == BTOR_OPT_SAT_ENGINE_LGL_FORK)
  {
    val = oldval;
    BTOR_MSG (btor->msg,
              1,
              "SAT solver Lingeling not compiled in, will not set option "
              "to clone/fork Lingeling");
  }
#endif
#ifndef NDEBUG
  else if (opt == BTOR_OPT_INCREMENTAL)
  {
    assert (btor->btor_sat_btor_called == 0);
  }
  else if (opt == BTOR_OPT_FUN_DUAL_PROP)
  {
    assert (!val || !btor_opt_get (btor, BTOR_OPT_FUN_JUST));
  }
  else if (opt == BTOR_OPT_FUN_JUST)
  {
    assert (!val || !btor_opt_get (btor, BTOR_OPT_FUN_DUAL_PROP));
  }
  else if (opt == BTOR_OPT_REWRITE_LEVEL)
  {
    assert (val <= 3);
    assert (oldval <= 3);
  }
#endif

  if (val > o->max) val = o->max;
  if (val < o->min) val = o->min;
  o->val = val;
}

void
btor_opt_set_str (Btor *btor, const BtorOption opt, const char *str)
{
  assert (btor);
  assert (btor_opt_is_valid (btor, opt));
  assert (opt == BTOR_OPT_SAT_ENGINE);

  btor->options[opt].valstr = btor_mem_strdup (btor->mm, str);
}

BtorOption
btor_opt_first (Btor *btor)
{
  assert (btor);
  (void) btor;
  return (BtorOption) 0;
}

BtorOption
btor_opt_next (Btor *btor, BtorOption cur)
{
  assert (btor);
  assert (btor_opt_is_valid (btor, cur));
  (void) btor;
  return (BtorOption) cur + 1;
}

#ifndef NBTORLOG
void
btor_opt_log_opts (Btor *btor)
{
  assert (btor);

  BtorOption opt;

  for (opt = btor_opt_first (btor); btor_opt_is_valid (btor, opt);
       opt = btor_opt_next (btor, opt))
    BTORLOG (2,
             "set option '%s' to %u",
             btor_opt_get_lng (btor, opt),
             btor_opt_get (btor, opt));
}
#endif
