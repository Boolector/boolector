/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2021 by the authors listed in the AUTHORS file.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORCORE_H_INCLUDED
#define BTORCORE_H_INCLUDED

#include "btorass.h"
#include "btormsg.h"
#include "btornode.h"
#include "btoropt.h"
#include "btorrwcache.h"
#include "btorsat.h"
#include "btorslv.h"
#include "btorsort.h"
#include "btortypes.h"
#include "utils/btorhashint.h"
#include "utils/btormem.h"
#include "utils/btorrng.h"

#include <stdbool.h>

/*------------------------------------------------------------------------*/

#ifndef BTOR_USE_LINGELING
#define BTOR_DO_NOT_PROCESS_SKELETON
#endif

// Currently, 'BoolectorNode' (external) vs. 'BtorNode' (internal)
// syntactically hides internal nodes.  Hence, we assume that both structs
// 'BoolectorNode' and 'BtorNode' have/ the same structure and provide the
// following macros for type conversion (via typecasting).  We further assume
// that external 'boolector_xxx' functions provide the same functionality as
// their internal counter part 'btor_xxx' (except for API tracing and contract
// checks).
//
// If the assumption above does not hold, we have to provide
// real containers for 'BoolectorNode' (cf. 'BoolectorNodeMap').

#define BTOR_IMPORT_BOOLECTOR_NODE(node) (((BtorNode *) (node)))
#define BTOR_IMPORT_BOOLECTOR_NODE_ARRAY(array) (((BtorNode **) (array)))
#define BTOR_EXPORT_BOOLECTOR_NODE(node) (((BoolectorNode *) (node)))
#define BTOR_IMPORT_BOOLECTOR_SORT(sort) (((BtorSortId) (long) (sort)))
#define BTOR_EXPORT_BOOLECTOR_SORT(sort) (((BoolectorSort) (long) (sort)))

/*------------------------------------------------------------------------*/

struct BtorNodeUniqueTable
{
  uint32_t size;
  uint32_t num_elements;
  BtorNode **chains;
};

typedef struct BtorNodeUniqueTable BtorNodeUniqueTable;

struct BtorCallbacks
{
  struct
  {
    /* the function to use for (checking) termination
     * (we need to distinguish between callbacks from C and Python) */
    int32_t (*termfun) (void *);

    void *fun;   /* termination callback function */
    void *state; /* termination callback function arguments */
    int32_t done;
  } term;
};

typedef struct BtorCallbacks BtorCallbacks;

struct BtorConstraintStats
{
  uint32_t varsubst;
  uint32_t embedded;
  uint32_t unsynthesized;
  uint32_t synthesized;
};

typedef struct BtorConstraintStats BtorConstraintStats;

struct Btor
{
  BtorMemMgr *mm;
  BtorSolver *slv;
  BtorCallbacks cbs;

  BtorBVAssList *bv_assignments;
  BtorFunAssList *fun_assignments;

  BtorNodePtrStack nodes_id_table;
  BtorNodeUniqueTable nodes_unique_table;
  BtorSortUniqueTable sorts_unique_table;

  BtorAIGVecMgr *avmgr;

  BtorPtrHashTable *symbols;
  BtorPtrHashTable *node2symbol;

  BtorPtrHashTable *inputs;
  BtorPtrHashTable *bv_vars;
  BtorPtrHashTable *ufs;
  BtorPtrHashTable *lambdas;
  BtorPtrHashTable *quantifiers;
  BtorPtrHashTable *exists_vars;
  BtorPtrHashTable *forall_vars;
  BtorPtrHashTable *feqs;
  BtorPtrHashTable *parameterized;

  BtorPtrHashTable *substitutions;

  BtorNode *true_exp;

  BtorIntHashTable *bv_model;
  BtorIntHashTable *fun_model;
  BtorNodePtrStack functions_with_model;
  BtorNodePtrStack outputs; /* used to synthesize BTOR2 outputs */

  uint32_t rec_rw_calls; /* calls for recursive rewriting */
  uint32_t valid_assignments;
  BtorRwCache *rw_cache;

  int32_t vis_idx; /* file index for visualizing expressions */

  bool inconsistent;
  bool found_constraint_false;

  uint32_t external_refs;        /* external references (library mode) */
  uint32_t btor_sat_btor_called; /* how often is btor_check_sat been called */
  BtorSolverResult last_sat_result; /* status of last SAT call (SAT/UNSAT) */

  BtorPtrHashTable *varsubst_constraints;
  BtorPtrHashTable *embedded_constraints;
  BtorPtrHashTable *unsynthesized_constraints;
  BtorPtrHashTable *synthesized_constraints;

  /* maintains simplified assumptions, these are the assumptions that are
   * actually bit-blasted and assumed to the SAT solver */
  BtorPtrHashTable *assumptions;
  /* maintains the non-simplified (original) assumptions */
  BtorPtrHashTable *orig_assumptions;
  /* maintains non-simplified assumptions as assumed via boolector_assume,
   * this stack is needed for boolector_get_failed_assumptions only */
  BtorNodePtrStack failed_assumptions;

  /* maintain assertions for different contexts push/pop */
  BtorNodePtrStack assertions;
  /* caches the assertions on stack 'assertions' */
  BtorIntHashTable *assertions_cache;
  /* saves the number of assertions on each push */
  BtorUIntStack assertions_trail;
  /* Number of push/pop calls (used for unique symbol prefixes) */
  uint32_t num_push_pop;

#ifndef NDEBUG
  Btor *clone; /* shadow clone (debugging only) */
#endif

  char *parse_error_msg;

  FILE *apitrace;
  int8_t close_apitrace;

  BtorOpt *options;
  BtorPtrHashTable *str2opt;

  BtorMsg *msg;
  BtorRNG rng;

  struct
  {
    uint32_t cur, max;
  } ops[BTOR_NUM_OPS_NODE];

  struct
  {
    uint32_t max_rec_rw_calls;  /* maximum number of recursive rewrite calls */
    uint32_t var_substitutions; /* number substituted vars */
    uint32_t uf_substitutions;  /* num substituted uninterpreted functions */
    uint32_t ec_substitutions;  /* embedded constraint substitutions */
    uint32_t linear_equations;  /* number of linear equations */
    uint32_t gaussian_eliminations; /* number of gaussian eliminations */
    uint32_t eliminated_slices;     /* number of eliminated slices */
    uint32_t skeleton_constraints;  /* number of skeleton constraints */
    uint32_t adds_normalized;       /* number of add chains normalizations */
    uint32_t ands_normalized;       /* number of and chains normalizations */
    uint32_t muls_normalized;       /* number of mul chains normalizations */
    uint32_t ackermann_constraints;
    uint_least64_t prop_apply_lambda; /* number of static props over lambdas */
    uint_least64_t prop_apply_update; /* number of static props over updates */
    uint32_t bv_uc_props;
    uint32_t fun_uc_props;
    uint32_t param_uc_props;
    uint_least64_t lambdas_merged;
    BtorConstraintStats constraints;
    BtorConstraintStats oldconstraints;
    uint_least64_t expressions;
    uint_least64_t clone_calls;
    size_t node_bytes_alloc;
    uint_least64_t beta_reduce_calls;
    uint_least64_t betap_reduce_calls;
#ifndef NDEBUG
    BtorPtrHashTable *rw_rules_applied;
#endif
    uint_least64_t rewrite_synth;
  } stats;

  struct
  {
    double sat;
    double simplify;
    double subst;
    double subst_rebuild;
    double elimapplies;
    double embedded;
    double slicing;
    double skel;
    double propagate;
    double beta;
    double betap;
    double failed;
    double cloning;
    double synth_exp;
    double model_gen;
    double ucopt;
    double merge;
    double extract;
    double ack;
    double rewrite;
    double occurrence;
  } time;
};

/* Creates new boolector instance. */
Btor *btor_new (void);

/* Deletes boolector. */
void btor_delete (Btor *btor);

/* Gets version. */
const char *btor_version (const Btor *btor);

/* Gets id. */
const char *btor_git_id (const Btor *btor);

/* Set termination callback. */
void btor_set_term (Btor *btor, int32_t (*fun) (void *), void *state);

/* Determine if boolector has been terminated via termination callback. */
int32_t btor_terminate (Btor *btor);

/* Set verbosity message prefix. */
void btor_set_msg_prefix (Btor *btor, const char *prefix);

/* Prints statistics. */
void btor_print_stats (Btor *btor);

/* Reset time statistics. */
void btor_reset_time (Btor *btor);

/* Reset other statistics. */
void btor_reset_stats (Btor *btor);

/* Adds top level constraint. */
void btor_assert_exp (Btor *btor, BtorNode *exp);

/* Adds assumption. */
void btor_assume_exp (Btor *btor, BtorNode *exp);

/* Determines if expression has been previously assumed. */
bool btor_is_assumption_exp (Btor *btor, BtorNode *exp);

/* Determines if assumption is a failed assumption. */
bool btor_failed_exp (Btor *btor, BtorNode *exp);

/* Adds assumptions as assertions and resets the assumptions. */
void btor_fixate_assumptions (Btor *btor);

/* Resets assumptions */
void btor_reset_assumptions (Btor *btor);

/* Solves instance, but with lemmas on demand limit 'lod_limit' and conflict
 * limit for the underlying SAT solver 'sat_limit'. */
int32_t btor_check_sat (Btor *btor, int32_t lod_limit, int32_t sat_limit);

BtorSATMgr *btor_get_sat_mgr (const Btor *btor);
BtorAIGMgr *btor_get_aig_mgr (const Btor *btor);

void btor_push (Btor *btor, uint32_t level);

void btor_pop (Btor *btor, uint32_t level);

/*------------------------------------------------------------------------*/

/* Check whether the sorts of given arguments match the signature of the
 * function. If sorts are correct -1 is returned, otherwise the position of
 * the invalid argument is returned. */
int32_t btor_fun_sort_check (Btor *btor,
                             BtorNode *args[],
                             uint32_t argc,
                             BtorNode *fun);

/* Synthesizes expression of arbitrary length to an AIG vector. Adds string
 * back annotation to the hash table, if the hash table is a non zero ptr.
 * The strings in 'data.asStr' are owned by the caller.  The hash table
 * is a map from AIG variables to strings.
 */
BtorAIGVec *btor_exp_to_aigvec (Btor *btor,
                                BtorNode *exp,
                                BtorPtrHashTable *table);

/* Checks for existing substitutions, finds most simplified expression and
 * shortens path to it */
BtorNode *btor_simplify_exp (Btor *btor, BtorNode *exp);

void btor_synthesize_exp (Btor *btor,
                          BtorNode *exp,
                          BtorPtrHashTable *backannotation);

/* Finds most simplified expression and shortens path to it */
BtorNode *btor_node_get_simplified (Btor *btor, BtorNode *exp);

void btor_release_all_ext_refs (Btor *btor);

void btor_init_substitutions (Btor *);
void btor_delete_substitutions (Btor *);
void btor_insert_substitution (Btor *, BtorNode *, BtorNode *, bool);
BtorNode *btor_find_substitution (Btor *, BtorNode *);

/* Create a new node with 'node' substituted by 'subst' in root. */
BtorNode *btor_substitute_node (Btor *btor,
                                BtorNode *root,
                                BtorNode *node,
                                BtorNode *subst);

/* Create a new node with 'substs' substituted in root. */
BtorNode *btor_substitute_nodes (Btor *btor,
                                 BtorNode *root,
                                 BtorNodeMap *substs);

/* Create a new term with 'substs' substituted in root. If 'node_map' is given
 * it creates an id map from old nodes to new nodes. */
BtorNode *btor_substitute_nodes_node_map (Btor *btor,
                                          BtorNode *root,
                                          BtorNodeMap *substs,
                                          BtorIntHashTable *node_map);

// TODO (ma): make these functions public until we have a common framework for
//            calling sat simplify etc.
void btor_reset_incremental_usage (Btor *btor);
void btor_add_again_assumptions (Btor *btor);
void btor_process_unsynthesized_constraints (Btor *btor);
void btor_insert_unsynthesized_constraint (Btor *btor, BtorNode *constraint);
void btor_set_simplified_exp (Btor *btor, BtorNode *exp, BtorNode *simplified);
void btor_delete_varsubst_constraints (Btor *btor);
#endif
