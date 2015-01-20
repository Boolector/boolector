/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2013 Armin Biere.
 *  Copyright (C) 2012-2014 Mathias Preiner.
 *  Copyright (C) 2012-2015 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORCORE_H_INCLUDED
#define BTORCORE_H_INCLUDED

#include "boolector.h"
#include "btorass.h"
#include "btorexp.h"
#include "btormem.h"
#include "btormsg.h"
#include "btoropt.h"
#include "btorsat.h"
#include "btorsort.h"

/*------------------------------------------------------------------------*/

#define BTOR_VERBOSITY_MAX 4

/*------------------------------------------------------------------------*/

//#define BTOR_DO_NOT_OPTIMIZE_UNCONSTRAINED

/*------------------------------------------------------------------------*/

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
#define BTOR_IMPORT_BOOLECTOR_SORT(sort) (((BtorSort *) (sort)))
#define BTOR_EXPORT_BOOLECTOR_SORT(sort) (((BoolectorSort *) (sort)))

/*------------------------------------------------------------------------*/

#define BOOLECTOR_IS_REGULAR_NODE BTOR_IS_INVERTED_NODE
#define BOOLECTOR_IS_INVERTED_NODE BTOR_IS_INVERTED_NODE

#define BOOLECTOR_REAL_ADDR_NODE(node) \
  BTOR_EXPORT_BOOLECTOR_NODE (         \
      BTOR_REAL_ADDR_NODE (BTOR_IMPORT_BOOLECTOR_NODE (node)))

#define BOOLECTOR_INVERT_NODE(node) \
  BTOR_EXPORT_BOOLECTOR_NODE (      \
      BTOR_INVERT_NODE (BTOR_IMPORT_BOOLECTOR_NODE (node)))

/*------------------------------------------------------------------------*/

struct BtorNodeUniqueTable
{
  int size;
  int num_elements;
  BtorNode **chains;
};

typedef struct BtorNodeUniqueTable BtorNodeUniqueTable;

struct ConstraintStats
{
  int varsubst;
  int embedded;
  int unsynthesized;
  int synthesized;
};

typedef struct ConstraintStats ConstraintStats;

enum BtorUAMode
{
  BTOR_UA_GLOBAL_MODE = 0,
  BTOR_UA_LOCAL_MODE,
  BTOR_UA_LOCAL_INDIVIDUAL_MODE
};

typedef enum BtorUAMode BtorUAMode;

enum BtorUARef
{
  BTOR_UA_REF_BY_DOUBLING = 0,
  BTOR_UA_REF_BY_INC_ONE
};

typedef enum BtorUARef BtorUARef;

enum BtorUAEnc
{
  BTOR_UA_ENC_SIGN_EXTEND = 0,
  BTOR_UA_ENC_ZERO_EXTEND,
  BTOR_UA_ENC_ONE_EXTEND,
  BTOR_UA_ENC_EQ_CLASSES
};

typedef enum BtorUAEnc BtorUAEnc;

// TODO (ma): array_assignments -> fun_assignments
struct Btor
{
  BtorMemMgr *mm;

  BtorBVAssignmentList *bv_assignments;
  BtorArrayAssignmentList *array_assignments;
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
  BtorPtrHashTable *substitutions;
  BtorNode *true_exp;
  BtorPtrHashTable *bv_model;
  BtorPtrHashTable *fun_model;

  int rec_rw_calls; /* calls for recursive rewriting */
  int rec_read_acond_calls;
  int valid_assignments;
  int vis_idx; /* file index for visualizing expressions */
  int vread_index_id;
  int inconsistent;
  int found_constraint_false;
  int external_refs;        /* external references (library mode) */
  int btor_sat_btor_called; /* how often is btor_sat_btor been called */
  int last_sat_result;      /* status of last SAT call (SAT/UNSAT) */

  BtorPtrHashTable *lod_cache;

  BtorPtrHashTable *varsubst_constraints;
  BtorPtrHashTable *embedded_constraints;
  BtorPtrHashTable *unsynthesized_constraints;
  BtorPtrHashTable *synthesized_constraints;
  BtorPtrHashTable *assumptions;
  BtorPtrHashTable *var_rhs;
  BtorPtrHashTable *fun_rhs;
  BtorNodePtrStack functions_with_model;
  BtorPtrHashTable *cache;
  BtorPtrHashTable *parameterized;
  BtorPtrHashTable *score;
  BtorPtrHashTable *searched_applies;

  /* compare fun for sorting the inputs in search_inital_applies_dual_prop */
  int (*dp_cmp_inputs) (const void *, const void *);

  /* shadow clone (debugging only) */
  Btor *clone;

  char *parse_error_msg;

  FILE *apitrace;
  int close_apitrace;

  /* statistics */
  struct
  {
    int max_rec_rw_calls; /* maximum number of recursive rewrite calls */
    int lod_refinements;  /* number of lemmas on demand refinements */
    int synthesis_assignment_inconsistencies; /* number of restarts as a
                                                 result of lazy synthesis */
    int synthesis_inconsistency_apply;
    int synthesis_inconsistency_lambda;
    int synthesis_inconsistency_var;
    int function_congruence_conflicts;
    int beta_reduction_conflicts;
#ifndef BTOR_DO_NOT_OPTIMIZE_UNCONSTRAINED
    int bv_uc_props;
    int fun_uc_props;
#endif
    int var_substitutions;     /* number substituted vars */
    int uf_substitutions;      /* num substituted uninterpreted functions */
    int ec_substitutions;      /* embedded constraint substitutions */
    int vreads;                /* number of virtual reads */
    int linear_equations;      /* number of linear equations */
    int gaussian_eliminations; /* number of gaussian eliminations */
    int eliminated_slices;     /* number of eliminated slices */
    int skeleton_constraints;  /* number of extracted skeleton constraints */
    int adds_normalized;       /* number of add chains normalizations */
    int ands_normalized;       /* number of and chains normalizations */
    int muls_normalized;       /* number of mul chains normalizations */
    int read_props_construct;  /* how often have we pushed a read over
                                  write during construction */
    int dp_failed_vars;        /* number of vars in FA (dual prop) of last
                                  sat call (final bv skeleton) */
    int dp_assumed_vars;
    int dp_failed_applies; /* number of applies in FA (dual prop) of last
                              sat call (final bv skeleton) */
    int dp_assumed_applies;
    BtorIntStack lemmas_size;       /* distribution of n-size lemmas */
    long long int lemmas_size_sum;  /* sum of the size of all added lemmas */
    long long int lclause_size_sum; /* sum of the size of all linking clauses */
    ConstraintStats constraints;
    ConstraintStats oldconstraints;
    long long expressions;
    long long beta_reduce_calls;
    long long eval_exp_calls;
    long long lambda_synth_apps;
    long long lambdas_merged;
    long long propagations;
    long long propagations_down;
    long long apply_props_construct;
    long long partial_beta_reduction_restarts;
  } stats;

  struct
  {
    int cur, max;
  } ops[BTOR_NUM_OPS_NODE];

  struct
  {
    double rewrite;
    double sat;
    double subst;
    double betareduce;
    double embedded;
    double slicing;
    double skel;
    double beta;
    double eval;
    double enc_app;
    double enc_lambda;
    double enc_var;
    double find_dfs;
    double reachable;
    double failed;
    double search_init_apps;
    double search_init_apps_compute_scores;
    double search_init_apps_compute_scores_merge_applies;
    double search_init_apps_cloning;
    double search_init_apps_sat;
    double search_init_apps_collect_var_apps;
    double search_init_apps_collect_fa;
    double search_init_apps_collect_fa_cone;
    double lemma_gen;
    double find_nenc_app;
    double find_prop_app;
    double find_cond_prop_app;
    double cloning;
    double synth_exp;
    double model_gen;
    double br_probing;
#ifndef BTOR_DO_NOT_OPTIMIZE_UNCONSTRAINED
    double ucopt;
#endif
  } time;

  BtorOpts options;
  BtorMsg *msg;
};

/* Creates new boolector instance. */
Btor *btor_new_btor (void);

/* Creates new boolector instance without initializing options. */
Btor *btor_new_btor_no_init (void);

/* Deletes boolector. */
void btor_delete_btor (Btor *btor);

/* Gets version. */
const char *btor_version (Btor *btor);

/* Set verbosity message prefix. */
void btor_set_msg_prefix_btor (Btor *btor, const char *prefix);

/* Prints statistics. */
void btor_print_stats_btor (Btor *btor);

/* Reset time statistics. */
void btor_reset_time_btor (Btor *btor);

/* Reset other statistics. */
void btor_reset_stats_btor (Btor *btor);

/* Adds top level constraint. */
void btor_assert_exp (Btor *btor, BtorNode *exp);

/* Adds assumption. */
void btor_assume_exp (Btor *btor, BtorNode *exp);

/* Determines if expression has been previously assumed. */
int btor_is_assumption_exp (Btor *btor, BtorNode *exp);

/* Determines if assumption is a failed assumption. */
int btor_failed_exp (Btor *btor, BtorNode *exp);

/* Solves instance, but with lemmas on demand limit 'lod_limit' and conflict
 * limit for the underlying SAT solver 'sat_limit'. */
int btor_sat_btor (Btor *btor, int lod_limit, int sat_limit);

BtorSATMgr *btor_get_sat_mgr_btor (const Btor *btor);

/* Run rewriting engine */
int btor_simplify (Btor *btor);

/*------------------------------------------------------------------------*/

/* Check whether the sorts of given arguments match the signature of the
 * function. If sorts are correct -1 is returned, otherwise the position of
 * the invalid argument is returned. */
int btor_fun_sort_check (Btor *btor, int argc, BtorNode **args, BtorNode *fun);

/* Evaluates expression and returns its value. */
char *btor_eval_exp (Btor *btor, BtorNode *exp);

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

/* Finds most simplified expression and shortens path to it */
BtorNode *btor_pointer_chase_simplified_exp (Btor *btor, BtorNode *exp);

int btor_is_equal_sort (Btor *btor, BtorNode *e0, BtorNode *e1);

/* Frees BV assignment obtained by calling 'btor_assignment_exp' */
void btor_release_bv_assignment_str (Btor *btor, char *assignment);

void btor_release_all_ext_refs (Btor *btor);

// TODO: eliminate when we have full sort support (ma)
BtorSort *btor_create_or_get_sort (Btor *, BtorNode *);

#endif
