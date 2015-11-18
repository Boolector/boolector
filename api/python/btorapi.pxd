# Boolector: Satisfiablity Modulo Theories (SMT) solver.
#
# Copyright (C) 2013-2014 Mathias Preiner.
# Copyright (C) 2014-2015 Aina Niemetz.
#
# All rights reserved.
#
# This file is part of Boolector.
# See COPYING for more information on using this software.
#

# TODO: check functions that are implemented

from libc.stdio cimport FILE
from libcpp cimport bool
from cpython.ref cimport PyObject

cdef extern from "boolector_py.h":
    void boolector_py_delete (Btor * btor)
    void boolector_py_set_term (Btor * btor, PyObject * fun, PyObject * state)

cdef extern from "boolector.h":
    ctypedef struct BoolectorNode:
        pass
    ctypedef struct Btor:
        pass
    ctypedef struct BoolectorSort:
        pass

    Btor *boolector_new ()

    Btor *boolector_clone (Btor * btor)

    void boolector_set_term (Btor * btor, int (*fun) (void *), void * state)

    int boolector_terminate (Btor * btor)

#    void boolector_set_msg_prefix (Btor * btor, const char * prefix)

    int boolector_get_refs (Btor * btor)

    void boolector_reset_time (Btor * btor)

    void boolector_reset_stats (Btor * btor)

    void boolector_print_stats (Btor * btor)

#    void boolector_set_trapi (Btor * btor, FILE * apitrace)

#    FILE *boolector_get_trapi (Btor * btor)

    void boolector_assert (Btor * btor, BoolectorNode * node)

    void boolector_assume (Btor * btor, BoolectorNode * node)

    int boolector_failed (Btor * btor, BoolectorNode * node)

    void boolector_fixate_assumptions (Btor * btor)

    void boolector_reset_assumptions (Btor * btor)

    int boolector_sat (Btor * btor)

    int boolector_limited_sat (Btor * btor, int lod_limit, int sat_limit)

    int boolector_simplify (Btor * btor)

    int boolector_set_sat_solver (Btor * btor, const char * solver)

    int boolector_set_sat_solver_lingeling (Btor * btor, const char * optstr,
                                            int nofork)

    void boolector_set_opt (Btor * btor, const char * opt, int val)

    int boolector_get_opt_val (Btor * btor, const char * opt)

    int boolector_get_opt_min (Btor * btor, const char * opt)

    int boolector_get_opt_max (Btor * btor, const char * opt)

    int boolector_get_opt_dflt (Btor * btor, const char * opt)

    const char * boolector_get_opt_shrt (Btor * btor, const char * opt)

    const char * boolector_get_opt_desc (Btor * btor, const char * opt)

    const char * boolector_first_opt (Btor * btor)

    const char * boolector_next_opt (Btor * btor, const char * opt)

    BoolectorNode *boolector_copy (Btor * btor, BoolectorNode * node)

    void boolector_release (Btor * btor, BoolectorNode * node)

    BoolectorNode *boolector_const (Btor * btor, const char *bits)

#    BoolectorNode *boolector_zero (Btor * btor, int width)

    BoolectorNode *boolector_false (Btor * btor)

#    BoolectorNode *boolector_ones (Btor * btor, int width)

    BoolectorNode *boolector_true (Btor * btor)

#    BoolectorNode *boolector_one (Btor * btor, int width)

#    BoolectorNode *boolector_unsigned_int (Btor * btor, unsigned u, int width)

#    BoolectorNode *boolector_int (Btor * btor, int i, int width)

    BoolectorNode *boolector_var (Btor * btor, int width, const char *symbol)

    BoolectorNode *boolector_array (Btor * btor, 
                                   int elem_width, 
                                   int index_width, 
                                   const char *symbol)

    BoolectorNode *boolector_not (Btor * btor, BoolectorNode * node)

    BoolectorNode *boolector_neg (Btor * btor, BoolectorNode * node)

    BoolectorNode *boolector_redor (Btor * btor, BoolectorNode * node)

    BoolectorNode *boolector_redxor (Btor * btor, BoolectorNode * node)

    BoolectorNode *boolector_redand (Btor * btor, BoolectorNode * node)

    BoolectorNode *boolector_slice (
        Btor * btor, BoolectorNode * node, int upper, int lower)

    BoolectorNode *boolector_uext (Btor * btor, BoolectorNode * node, int width)

    BoolectorNode *boolector_sext (Btor * btor, BoolectorNode * node, int width)

    BoolectorNode *boolector_implies (
        Btor * btor, BoolectorNode * n0, BoolectorNode * n1)

    BoolectorNode *boolector_iff (
        Btor * btor, BoolectorNode * n0, BoolectorNode * n1)

    BoolectorNode *boolector_xor (
        Btor * btor, BoolectorNode * n0, BoolectorNode * n1)

    BoolectorNode *boolector_xnor (
        Btor * btor, BoolectorNode * n0, BoolectorNode * n1)

    BoolectorNode *boolector_and (
        Btor * btor, BoolectorNode * n0, BoolectorNode * n1)

    BoolectorNode *boolector_nand (
        Btor * btor, BoolectorNode * n0, BoolectorNode * n1)

    BoolectorNode *boolector_or (
        Btor * btor, BoolectorNode * n0, BoolectorNode * n1)

    BoolectorNode *boolector_nor (
        Btor * btor, BoolectorNode * n0, BoolectorNode * n1)

    BoolectorNode *boolector_eq (
        Btor * btor, BoolectorNode * n0, BoolectorNode * n1)

    BoolectorNode *boolector_ne (
        Btor * btor, BoolectorNode * n0, BoolectorNode * n1)

    BoolectorNode *boolector_add (
        Btor * btor, BoolectorNode * n0, BoolectorNode * n1)

    BoolectorNode *boolector_uaddo (
        Btor * btor, BoolectorNode * n0, BoolectorNode * n1)

    BoolectorNode *boolector_saddo (
        Btor * btor, BoolectorNode * n0, BoolectorNode * n1)

    BoolectorNode *boolector_mul (
        Btor * btor, BoolectorNode * n0, BoolectorNode * n1)

    BoolectorNode *boolector_umulo (
        Btor * btor, BoolectorNode * n0, BoolectorNode * n1)

    BoolectorNode *boolector_smulo (
        Btor * btor, BoolectorNode * n0, BoolectorNode * n1)

    BoolectorNode *boolector_ult (
        Btor * btor, BoolectorNode * n0, BoolectorNode * n1)

    BoolectorNode *boolector_slt (
        Btor * btor, BoolectorNode * n0, BoolectorNode * n1)

    BoolectorNode *boolector_ulte (
        Btor * btor, BoolectorNode * n0, BoolectorNode * n1)

    BoolectorNode *boolector_slte (
        Btor * btor, BoolectorNode * n0, BoolectorNode * n1)

    BoolectorNode *boolector_ugt (
        Btor * btor, BoolectorNode * n0, BoolectorNode * n1)

    BoolectorNode *boolector_sgt (
        Btor * btor, BoolectorNode * n0, BoolectorNode * n1)

    BoolectorNode *boolector_ugte (
        Btor * btor, BoolectorNode * n0, BoolectorNode * n1)

    BoolectorNode *boolector_sgte (
        Btor * btor, BoolectorNode * n0, BoolectorNode * n1)

    BoolectorNode *boolector_sll (
        Btor * btor, BoolectorNode * n0, BoolectorNode * n1)

    BoolectorNode *boolector_srl (
        Btor * btor, BoolectorNode * n0, BoolectorNode * n1)

    BoolectorNode *boolector_sra (
        Btor * btor, BoolectorNode * n0, BoolectorNode * n1)

    BoolectorNode *boolector_rol (
        Btor * btor, BoolectorNode * n0, BoolectorNode * n1)

    BoolectorNode *boolector_ror (
        Btor * btor, BoolectorNode * n0, BoolectorNode * n1)

    BoolectorNode *boolector_sub (
        Btor * btor, BoolectorNode * n0, BoolectorNode * n1)

    BoolectorNode *boolector_usubo (
        Btor * btor, BoolectorNode * n0, BoolectorNode * n1)

    BoolectorNode *boolector_ssubo (
        Btor * btor, BoolectorNode * n0, BoolectorNode * n1)

    BoolectorNode *boolector_udiv (
        Btor * btor, BoolectorNode * n0, BoolectorNode * n1)

    BoolectorNode *boolector_sdiv (
        Btor * btor, BoolectorNode * n0, BoolectorNode * n1)

    BoolectorNode *boolector_sdivo (
        Btor * btor, BoolectorNode * n0, BoolectorNode * n1)

    BoolectorNode *boolector_urem (
        Btor * btor, BoolectorNode * n0, BoolectorNode * n1)

    BoolectorNode *boolector_srem (
        Btor * btor, BoolectorNode * n0, BoolectorNode * n1)

    BoolectorNode *boolector_smod (
        Btor * btor, BoolectorNode * n0, BoolectorNode * n1)

    BoolectorNode *boolector_concat (
        Btor * btor, BoolectorNode * n0, BoolectorNode * n1)

    BoolectorNode *boolector_read (
        Btor * btor, BoolectorNode * n_array, BoolectorNode * n_index)

    BoolectorNode *boolector_write (Btor * btor, 
                                    BoolectorNode * n_array, 
                                    BoolectorNode * n_index, 
                                    BoolectorNode * n_value)

    BoolectorNode *boolector_cond (Btor * btor, 
                                   BoolectorNode * n_cond, 
                                   BoolectorNode * n_if, 
                                   BoolectorNode * n_else)

    BoolectorNode *boolector_param (Btor * btor, int width, const char * symbol) 

    BoolectorNode *boolector_fun (Btor * btor, 
                                  BoolectorNode ** param_nodes, 
                                  int paramc, 
                                  BoolectorNode * node) 

    BoolectorNode *boolector_uf (Btor * btor, BoolectorSort sort,
                                 const char * symbol)

    BoolectorNode *boolector_apply (Btor * btor,
                                    BoolectorNode ** arg_nodes,
                                    int argc,
                                    BoolectorNode * n_fun)

    BoolectorNode *boolector_inc (Btor * btor, BoolectorNode *node)

    BoolectorNode *boolector_dec (Btor * btor, BoolectorNode *node)

#    Btor *boolector_get_btor (BoolectorNode * node)

#    int boolector_get_id (Btor * btor, BoolectorNode * node)

#    BoolectorNode *boolector_match_node_by_id (Btor * btor, int id)

    BoolectorNode *boolector_match_node (Btor * btor, BoolectorNode * node)

    int boolector_is_const (Btor *btor, BoolectorNode * node)

#    int boolector_is_var (Btor * btor, BoolectorNode * node)

    const char * boolector_get_bits (Btor *, BoolectorNode * node)

    void boolector_free_bits (Btor *, const char * bits)

#    int boolector_is_array (Btor * btor, BoolectorNode * node)

#    int boolector_is_array_var (Btor * btor, BoolectorNode * node)

#    int boolector_is_param (Btor * btor, BoolectorNode * node)

#    int boolector_is_bound_param (Btor * btor, BoolectorNode * node)

#    int boolector_is_fun (Btor * btor, BoolectorNode * node)

    int boolector_get_fun_arity (Btor * btor, BoolectorNode * node)

    int boolector_get_width (Btor * btor, BoolectorNode * node)

    int boolector_get_index_width (Btor * btor, BoolectorNode * n_array)

    const char *boolector_get_symbol (Btor * btor, BoolectorNode * node)

    void boolector_set_symbol (Btor * btor, BoolectorNode * var,
                               const char * symbol)

    const char *boolector_bv_assignment (Btor * btor, BoolectorNode * node)

    void boolector_free_bv_assignment (Btor * btor, const char * assignment)

    void boolector_array_assignment (Btor * btor, 
                                     BoolectorNode * n_array, 
                                     char *** indices, 
                                     char *** values, 
                                     int * size)

    void boolector_free_array_assignment (
        Btor * btor, char ** indices, char ** values, int size)

    void boolector_uf_assignment (Btor * btor, 
                                  BoolectorNode * n_array, 
                                  char *** args, 
                                  char *** values, 
                                  int * size)

    void boolector_free_uf_assignment (
        Btor * btor, char ** args, char ** values, int size)

    void boolector_print_model (Btor * btor, char * format, FILE * file)

    BoolectorSort boolector_bool_sort (Btor * btor)

    BoolectorSort boolector_bitvec_sort (Btor * btor, int len)

    BoolectorSort boolector_fun_sort (Btor * btor,
                                      BoolectorSort * domain,
                                      int arity,
                                      BoolectorSort codomain)

    void boolector_release_sort (Btor * btor, BoolectorSort sort)

    int boolector_parse (Btor * btor, 
                         FILE * infile, 
                         const char * infile_name, 
                         FILE * outfile,
                         char ** error_msg,
                         int * status)

#    int boolector_parse_btor (Btor * btor,
#                              FILE * file, 
#                              const char * file_name, 
#                              char ** error_msg,
#                              int * status)
#
#    int boolector_parse_smt1 (Btor * btor, 
#                              FILE * file, 
#                              const char * file_name, 
#                              char ** error_msg,
#                              int * status)
#
#    int boolector_parse_smt2 (Btor * btor, 
#                              FILE * file, 
#                              const char * file_name, 
#                              char ** error_msg,
#                              int * status)

    void boolector_dump_btor_node (Btor * btor, FILE * file,
                                   BoolectorNode * node)

    void boolector_dump_btor (Btor * btor, FILE * file)

    void boolector_dump_smt2_node (Btor * btor, FILE * file,
                                   BoolectorNode * node)

    void boolector_dump_smt2 (Btor * btor, FILE * file)

    void boolector_dump_aiger_ascii (Btor * btor, FILE * file, bool merge_roots)

    void boolector_dump_aiger_binary (Btor * btor, FILE * file, bool merge_roots)
