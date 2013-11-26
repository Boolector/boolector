/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2013 Armin Biere.
 *  Copyright (C) 2012-2013 Aina Niemetz, Mathias Preiner.
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
#include "btorsort.h"

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

struct Btor
{
  BtorMemMgr *mm;
  BtorBVAssignmentList *bv_assignments;
  BtorArrayAssignmentList *array_assignments;
  BtorNodePtrStack nodes_id_table;
  BtorNodeUniqueTable nodes_unique_table;
  BtorSortUniqueTable sorts_unique_table;
  BtorAIGVecMgr *avmgr;
  BtorPtrHashTable *bv_vars;
  BtorPtrHashTable *array_vars;
  BtorPtrHashTable *lambdas;
  BtorPtrHashTable *substitutions;
  BtorNode *true_exp;
  int bv_lambda_id;    /* counter for lambda bv variables (subst) */
  int array_lambda_id; /* counter for lambda array variables (subst) */
  int dvn_id;          /* counter for vars (no symbol) via API */
  int dan_id;          /* counter for arrays (no symbol) via API */
  int dpn_id;          /* counter for params (no symbol) via API */
  int rec_rw_calls;    /* calls for recursive rewriting */
  int rec_read_acond_calls;
  int valid_assignments;
  int rewrite_level;
  int verbosity;
#ifndef NBTORLOG
  int loglevel;
#endif
  int vis_idx; /* file index for visualizing expressions */
  int vread_index_id;
  int inconsistent;
  int model_gen;            /* model generation enabled */
  int external_refs;        /* external references (library mode) */
  int inc_enabled;          /* incremental usage enabled ? */
  int btor_sat_btor_called; /* how often is btor_sat_btor been called */
  int msgtick;              /* message tick in incremental mode */
  int beta_reduce_all;      /* eliminate lambda expressions */
  int pprint;               /* reindex exps when dumping */
  int last_sat_result;      /* status of last SAT call (SAT/UNSAT) */

  int generate_model_for_all_reads;

  BtorPtrHashTable *lod_cache;

  BtorPtrHashTable *varsubst_constraints;
  BtorPtrHashTable *embedded_constraints;
  BtorPtrHashTable *unsynthesized_constraints;
  BtorPtrHashTable *synthesized_constraints;
  BtorPtrHashTable *assumptions;
  BtorPtrHashTable *var_rhs;   /* only for model generation */
  BtorPtrHashTable *array_rhs; /* only for model generation */
  BtorNodePtrStack arrays_with_model;
  BtorPtrHashTable *cache;
  BtorPtrHashTable *parameterized;

  /* shadow clone (debugging only) */
  Btor *clone;

  FILE *apitrace;
  int closeapitrace;

  /* statistics */
  int ops[BTOR_NUM_OPS_NODE];
  struct
  {
    int max_rec_rw_calls; /* maximum number of recursive rewrite calls */
    int lod_refinements;  /* number of lemmas on demand refinements */
    int synthesis_assignment_inconsistencies; /* number of restarts as a
                                                 result of lazy synthesis */
    int synthesis_inconsistency_apply;
    int synthesis_inconsistency_lambda;
    int synthesis_inconsistency_var;
    int array_axiom_1_conflicts; /* number of array axiom 1 conflicts:
                                    a = b /\ i = j => read(a, i) = read(b, j) */
    int array_axiom_2_conflicts; /* array axiom 2 confs:
                                    i = j => read(write(a, i, e), j) = e */
    int var_substitutions;       /* number substituted vars (non array) */
    int array_substitutions;     /* num substituted array vars */
    int ec_substitutions;        /* embedded constraint substitutions */
    int vreads;                  /* number of virtual reads */
    int linear_equations;        /* number of linear equations */
    int gaussian_eliminations;   /* number of gaussian eliminations */
    int eliminated_slices;       /* number of eliminated slices */
    int skeleton_constraints;    /* number of extracted skeleton constraints */
    int adds_normalized;         /* number of add chains normalizations */
    int ands_normalized;         /* number of and chains normalizations */
    int muls_normalized;         /* number of mul chains normalizations */
    int read_props_construct;    /* how often have we pushed a read over
                                    write during construction */
    long long int lemmas_size_sum;  /* sum of the size of all added lemmas */
    long long int lclause_size_sum; /* sum of the size of all linking clauses */
    ConstraintStats constraints, oldconstraints;
    long long expressions;
    long long beta_reduce_calls;
    long long eval_exp_calls;
    long long lambda_synth_apps;
    long long lambda_chains_merged;
    long long lambdas_merged;
    long long propagations;
    long long propagations_down;
    long long apply_props_construct;
  } stats;

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
  } time;
};

/* Creates new boolector instance. */
Btor *btor_new_btor (void);

/* Sets rewrite level [0,2]. */
void btor_set_rewrite_level_btor (Btor *btor, int rewrite_level);

/* Forces all reads to be synthesized during model generation. */
void btor_generate_model_for_all_reads (Btor *btor);

/* Enable rewriting of reads on lambda expressions. */
void btor_enable_beta_reduce_all (Btor *btor);

/* Disable pretty printing when dumping and rewriting of writes is enabled.  */
void btor_disable_pretty_print (Btor *btor);

/* Enables model generation. */
void btor_enable_model_gen (Btor *btor);

/* Enables incremental usage which means that assumptions are enabled
 * and btor_sat_btor can be called more than once. Note that enabling this
 * feature turns off some optimizations which are not possible anymore.
 */
void btor_enable_inc_usage (Btor *btor);

int btor_set_sat_solver (Btor *, const char *);

/* Sets verbosity [-1,3] of btor and all sub-components
 * if verbosity is set to -1, then boolector is in "quiet mode" and
 * does not print any output.
 */
void btor_set_verbosity_btor (Btor *btor, int verbosity);

/* Set log level.
 */
#ifndef NBTORLOG
void btor_set_loglevel_btor (Btor *btor, int loglevel);
#endif

/* Deletes boolector. */
void btor_delete_btor (Btor *btor);

/* Gets version. */
const char *btor_version (Btor *btor);

/* Prints statistics. */
void btor_print_stats_btor (Btor *btor);

/* Adds top level constraint. */
void btor_assert_exp (Btor *btor, BtorNode *exp);

/* Adds assumption. */
void btor_assume_exp (Btor *btor, BtorNode *exp);

/* Solves SAT instance.
 */
int btor_sat_btor (Btor *btor);

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

BtorAIG *btor_exp_to_aig (Btor *btor, BtorNode *exp);

/* Checks for existing substitutions, finds most simplified expression and
 * shortens path to it */
BtorNode *btor_simplify_exp (Btor *btor, BtorNode *exp);

/* Finds most simplified expression and shortens path to it */
BtorNode *btor_pointer_chase_simplified_exp (Btor *btor, BtorNode *exp);

#endif
