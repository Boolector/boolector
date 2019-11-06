# Boolector: Satisfiablity Modulo Theories (SMT) solver.
#
# Copyright (C) 2013-2018 Mathias Preiner.
# Copyright (C) 2014-2018 Aina Niemetz.
#
# This file is part of Boolector.
# See COPYING for more information on using this software.
#


from libc.stdio cimport FILE
from libcpp cimport bool
from cpython.ref cimport PyObject
from libc.stdint cimport int32_t, uint32_t
from pyboolector import BoolectorException

#include "pyboolector_options.pxd"

cdef inline int raise_py_error() except *:
    raise BoolectorException(pyboolector_get_err_msg().decode('utf-8'))

cdef extern from "pyboolector_abort.h":
    void pyboolector_abort_fun (const char* msg)
    const char * pyboolector_get_err_msg ()

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
    ctypedef enum BtorOption:
        pass

    Btor *boolector_new () \
      except +raise_py_error

    Btor *boolector_clone (Btor * btor) \
      except +raise_py_error

    void boolector_set_abort (void (*fun) (const char *msg)) \
      except +raise_py_error

    void boolector_set_term (Btor * btor,
                             int32_t (*fun) (void *),
                             void * state) \
      except +raise_py_error

    int32_t boolector_terminate (Btor * btor) \
      except +raise_py_error

    #void boolector_set_msg_prefix (Btor * btor,
    #                               const char * prefix) \
    #  except +raise_py_error

    uint32_t boolector_get_refs (Btor * btor) \
      except +raise_py_error

    void boolector_reset_time (Btor * btor) \
      except +raise_py_error

    void boolector_reset_stats (Btor * btor) \
      except +raise_py_error

    void boolector_print_stats (Btor * btor) \
      except +raise_py_error

    #void boolector_set_trapi (Btor * btor,
    #                          FILE * apitrace) \
    #  except +raise_py_error

    #FILE *boolector_get_trapi (Btor * btor) \
    #  except +raise_py_error

    void boolector_push (Btor * btor, uint32_t level) \
      except +raise_py_error

    void boolector_pop (Btor * btor, uint32_t level) \
      except +raise_py_error

    void boolector_assert (Btor * btor, BoolectorNode * node) \
      except +raise_py_error

    void boolector_assume (Btor * btor, BoolectorNode * node) \
      except +raise_py_error

    bool boolector_failed (Btor * btor, BoolectorNode * node) \
      except +raise_py_error

    void boolector_fixate_assumptions (Btor * btor) \
      except +raise_py_error

    void boolector_reset_assumptions (Btor * btor) \
      except +raise_py_error

    int32_t boolector_sat (Btor * btor) \
      except +raise_py_error

    int32_t boolector_limited_sat (Btor * btor,
                                   int32_t lod_limit,
                                   int32_t sat_limit) \
      except +raise_py_error

    int32_t boolector_simplify (Btor * btor) \
      except +raise_py_error

    void boolector_set_sat_solver (Btor * btor, const char * solver) \
      except +raise_py_error

    void boolector_set_opt (Btor * btor, BtorOption opt, uint32_t val) \
      except +raise_py_error

    uint32_t boolector_get_opt (Btor * btor, BtorOption opt) \
      except +raise_py_error

    uint32_t boolector_get_opt_min (Btor * btor, BtorOption opt) \
      except +raise_py_error

    uint32_t boolector_get_opt_max (Btor * btor, BtorOption opt) \
      except +raise_py_error

    uint32_t boolector_get_opt_dflt (Btor * btor, BtorOption opt) \
      except +raise_py_error

    const char * boolector_get_opt_shrt (Btor * btor, BtorOption opt) \
      except +raise_py_error

    const char * boolector_get_opt_lng (Btor * btor, BtorOption opt) \
      except +raise_py_error

    const char * boolector_get_opt_desc (Btor * btor, BtorOption opt) \
      except +raise_py_error

    BtorOption boolector_first_opt (Btor * btor) \
      except +raise_py_error

    BtorOption boolector_next_opt (Btor * btor, BtorOption opt) \
      except +raise_py_error

    bool boolector_has_opt (Btor * btor, BtorOption opt) \
      except +raise_py_error

    BoolectorNode *boolector_copy (Btor * btor, BoolectorNode * node) \
      except +raise_py_error

    void boolector_release (Btor * btor, BoolectorNode * node) \
      except +raise_py_error

    BoolectorNode *boolector_const (Btor * btor, const char *bits) \
      except +raise_py_error

    #BoolectorNode *boolector_zero (Btor * btor, BoolectorSort sort) \
    #  except +raise_py_error

    BoolectorNode *boolector_false (Btor * btor) \
      except +raise_py_error

    #BoolectorNode *boolector_ones (Btor * btor, BoolectorSort sort) \
    #  except +raise_py_error

    BoolectorNode *boolector_true (Btor * btor) \
      except +raise_py_error

    #BoolectorNode *boolector_one (Btor * btor, BoolectorSort sort) \
    #  except +raise_py_error

    #BoolectorNode *boolector_unsigned_int (Btor * btor, uint32_t u, BoolectorSort sort) \
    #  except +raise_py_error

    #BoolectorNode *boolector_int (Btor * btor, int32_t i, BoolectorSort sort) \
    #  except +raise_py_error

    BoolectorNode *boolector_var (
        Btor * btor, BoolectorSort sort, const char *symbol) \
      except +raise_py_error

    BoolectorNode *boolector_array (
        Btor * btor, BoolectorSort  sort, const char *symbol) \
      except +raise_py_error

    BoolectorNode *boolector_const_array (
        Btor * btor,
        BoolectorSort  sort,
        BoolectorNode * value) \
      except +raise_py_error

    BoolectorNode *boolector_not (
        Btor * btor, BoolectorNode * node) \
      except +raise_py_error

    BoolectorNode *boolector_neg (
        Btor * btor, BoolectorNode * node) \
      except +raise_py_error

    BoolectorNode *boolector_redor (
        Btor * btor, BoolectorNode * node) \
      except +raise_py_error

    BoolectorNode *boolector_redxor (
        Btor * btor, BoolectorNode * node) \
      except +raise_py_error

    BoolectorNode *boolector_redand (
        Btor * btor, BoolectorNode * node) \
      except +raise_py_error

    BoolectorNode *boolector_slice (
        Btor * btor, BoolectorNode * node, uint32_t upper, uint32_t lower) \
      except +raise_py_error

    BoolectorNode *boolector_uext (
        Btor * btor, BoolectorNode * node, uint32_t width) \
      except +raise_py_error

    BoolectorNode *boolector_sext (
        Btor * btor, BoolectorNode * node, uint32_t width) \
      except +raise_py_error

    BoolectorNode *boolector_implies (
        Btor * btor, BoolectorNode * n0, BoolectorNode * n1) \
      except +raise_py_error

    BoolectorNode *boolector_iff (
        Btor * btor, BoolectorNode * n0, BoolectorNode * n1) \
      except +raise_py_error

    BoolectorNode *boolector_xor (
        Btor * btor, BoolectorNode * n0, BoolectorNode * n1) \
      except +raise_py_error

    BoolectorNode *boolector_xnor (
        Btor * btor, BoolectorNode * n0, BoolectorNode * n1) \
      except +raise_py_error

    BoolectorNode *boolector_and (
        Btor * btor, BoolectorNode * n0, BoolectorNode * n1) \
      except +raise_py_error

    BoolectorNode *boolector_nand (
        Btor * btor, BoolectorNode * n0, BoolectorNode * n1) \
      except +raise_py_error

    BoolectorNode *boolector_or (
        Btor * btor, BoolectorNode * n0, BoolectorNode * n1) \
      except +raise_py_error

    BoolectorNode *boolector_nor (
        Btor * btor, BoolectorNode * n0, BoolectorNode * n1) \
      except +raise_py_error

    BoolectorNode *boolector_eq (
        Btor * btor, BoolectorNode * n0, BoolectorNode * n1) \
      except +raise_py_error

    BoolectorNode *boolector_ne (
        Btor * btor, BoolectorNode * n0, BoolectorNode * n1) \
      except +raise_py_error

    BoolectorNode *boolector_add (
        Btor * btor, BoolectorNode * n0, BoolectorNode * n1) \
      except +raise_py_error

    BoolectorNode *boolector_uaddo (
        Btor * btor, BoolectorNode * n0, BoolectorNode * n1) \
      except +raise_py_error

    BoolectorNode *boolector_saddo (
        Btor * btor, BoolectorNode * n0, BoolectorNode * n1) \
      except +raise_py_error

    BoolectorNode *boolector_mul (
        Btor * btor, BoolectorNode * n0, BoolectorNode * n1) \
      except +raise_py_error

    BoolectorNode *boolector_umulo (
        Btor * btor, BoolectorNode * n0, BoolectorNode * n1) \
      except +raise_py_error

    BoolectorNode *boolector_smulo (
        Btor * btor, BoolectorNode * n0, BoolectorNode * n1) \
      except +raise_py_error

    BoolectorNode *boolector_ult (
        Btor * btor, BoolectorNode * n0, BoolectorNode * n1) \
      except +raise_py_error

    BoolectorNode *boolector_slt (
        Btor * btor, BoolectorNode * n0, BoolectorNode * n1) \
      except +raise_py_error

    BoolectorNode *boolector_ulte (
        Btor * btor, BoolectorNode * n0, BoolectorNode * n1) \
      except +raise_py_error

    BoolectorNode *boolector_slte (
        Btor * btor, BoolectorNode * n0, BoolectorNode * n1) \
      except +raise_py_error

    BoolectorNode *boolector_ugt (
        Btor * btor, BoolectorNode * n0, BoolectorNode * n1) \
      except +raise_py_error

    BoolectorNode *boolector_sgt (
        Btor * btor, BoolectorNode * n0, BoolectorNode * n1) \
      except +raise_py_error

    BoolectorNode *boolector_ugte (
        Btor * btor, BoolectorNode * n0, BoolectorNode * n1) \
      except +raise_py_error

    BoolectorNode *boolector_sgte (
        Btor * btor, BoolectorNode * n0, BoolectorNode * n1) \
      except +raise_py_error

    BoolectorNode *boolector_sll (
        Btor * btor, BoolectorNode * n0, BoolectorNode * n1) \
      except +raise_py_error

    BoolectorNode *boolector_srl (
        Btor * btor, BoolectorNode * n0, BoolectorNode * n1) \
      except +raise_py_error

    BoolectorNode *boolector_sra (
        Btor * btor, BoolectorNode * n0, BoolectorNode * n1) \
      except +raise_py_error

    BoolectorNode *boolector_rol (
        Btor * btor, BoolectorNode * n0, BoolectorNode * n1) \
      except +raise_py_error

    BoolectorNode *boolector_ror (
        Btor * btor, BoolectorNode * n0, BoolectorNode * n1) \
      except +raise_py_error

    BoolectorNode *boolector_sub (
        Btor * btor, BoolectorNode * n0, BoolectorNode * n1) \
      except +raise_py_error

    BoolectorNode *boolector_usubo (
        Btor * btor, BoolectorNode * n0, BoolectorNode * n1) \
      except +raise_py_error

    BoolectorNode *boolector_ssubo (
        Btor * btor, BoolectorNode * n0, BoolectorNode * n1) \
      except +raise_py_error

    BoolectorNode *boolector_udiv (
        Btor * btor, BoolectorNode * n0, BoolectorNode * n1) \
      except +raise_py_error

    BoolectorNode *boolector_sdiv (
        Btor * btor, BoolectorNode * n0, BoolectorNode * n1) \
      except +raise_py_error

    BoolectorNode *boolector_sdivo (
        Btor * btor, BoolectorNode * n0, BoolectorNode * n1) \
      except +raise_py_error

    BoolectorNode *boolector_urem (
        Btor * btor, BoolectorNode * n0, BoolectorNode * n1) \
      except +raise_py_error

    BoolectorNode *boolector_srem (
        Btor * btor, BoolectorNode * n0, BoolectorNode * n1) \
      except +raise_py_error

    BoolectorNode *boolector_smod (
        Btor * btor, BoolectorNode * n0, BoolectorNode * n1) \
      except +raise_py_error

    BoolectorNode *boolector_concat (
        Btor * btor, BoolectorNode * n0, BoolectorNode * n1) \
      except +raise_py_error

    BoolectorNode *boolector_repeat (
        Btor * btor, BoolectorNode * node, uint32_t n) \
      except +raise_py_error

    BoolectorNode *boolector_read (
        Btor * btor, BoolectorNode * n_array, BoolectorNode * n_index) \
      except +raise_py_error

    BoolectorNode *boolector_write (Btor * btor,
                                    BoolectorNode * n_array,
                                    BoolectorNode * n_index,
                                    BoolectorNode * n_value) \
      except +raise_py_error

    BoolectorNode *boolector_cond (Btor * btor,
                                   BoolectorNode * n_cond,
                                   BoolectorNode * n_if,
                                   BoolectorNode * n_else) \
      except +raise_py_error

    BoolectorNode *boolector_param (
            Btor * btor, BoolectorSort sort, const char * symbol)

    BoolectorNode *boolector_fun (Btor * btor,
                                  BoolectorNode ** param_nodes,
                                  uint32_t paramc,
                                  BoolectorNode * node)

    BoolectorNode *boolector_uf (Btor * btor, BoolectorSort sort,
                                 const char * symbol) \
      except +raise_py_error

    BoolectorNode *boolector_apply (Btor * btor,
                                    BoolectorNode ** arg_nodes,
                                    uint32_t argc,
                                    BoolectorNode * n_fun) \
      except +raise_py_error

    BoolectorNode *boolector_inc (Btor * btor, BoolectorNode *node) \
      except +raise_py_error

    BoolectorNode *boolector_dec (Btor * btor, BoolectorNode *node) \
      except +raise_py_error

    BoolectorNode *boolector_forall (Btor *btor,
                                     BoolectorNode *params[],
                                     uint32_t paramc,
                                     BoolectorNode *body) \
      except +raise_py_error

    BoolectorNode *boolector_exists (Btor *btor,
                                     BoolectorNode *param[],
                                     uint32_t paramc,
                                     BoolectorNode *body) \
      except +raise_py_error

    #Btor *boolector_get_btor (BoolectorNode * node) \
    #  except +raise_py_error

    #uint32_t boolector_get_node_id (Btor * btor, BoolectorNode * node) \
    #  except +raise_py_error

    #BoolectorNode *boolector_match_node_by_id (Btor * btor, int32_t id) \
    #  except +raise_py_error

    BoolectorNode *boolector_match_node_by_symbol (Btor * btor, char * sym) \
      except +raise_py_error

    BoolectorNode *boolector_match_node (Btor * btor, BoolectorNode * node) \
      except +raise_py_error

    bool boolector_is_const (Btor *btor, BoolectorNode * node) \
      except +raise_py_error

    #bool boolector_is_var (Btor * btor, BoolectorNode * node) \
    #  except +raise_py_error

    const char * boolector_get_bits (Btor * btor, BoolectorNode * node) \
      except +raise_py_error

    void boolector_free_bits (Btor * btor, const char * bits) \
      except +raise_py_error

    #bool boolector_is_array (Btor * btor, BoolectorNode * node) \
    #  except +raise_py_error

    #bool boolector_is_array_var (Btor * btor, BoolectorNode * node) \
    #  except +raise_py_error

    #bool boolector_is_param (Btor * btor, BoolectorNode * node) \
    #  except +raise_py_error

    #bool boolector_is_bound_param (Btor * btor, BoolectorNode * node) \
    #  except +raise_py_error

    #bool boolector_is_fun (Btor * btor, BoolectorNode * node) \
    #  except +raise_py_error

    uint32_t boolector_get_fun_arity (Btor * btor, BoolectorNode * node) \
      except +raise_py_error

    uint32_t boolector_get_width (Btor * btor, BoolectorNode * node) \
      except +raise_py_error

    uint32_t boolector_get_index_width (Btor * btor, BoolectorNode * n_array) \
      except +raise_py_error

    const char *boolector_get_symbol (Btor * btor, BoolectorNode * node) \
      except +raise_py_error

    void boolector_set_symbol (Btor * btor, BoolectorNode * var,
                               const char * symbol) \
      except +raise_py_error

    const char *boolector_bv_assignment (Btor * btor, BoolectorNode * node) \
      except +raise_py_error

    void boolector_free_bv_assignment (Btor * btor, const char * assignment) \
      except +raise_py_error

    void boolector_array_assignment (Btor * btor,
                                     BoolectorNode * n_array,
                                     char *** indices,
                                     char *** values,
                                     uint32_t * size) \
      except +raise_py_error

    void boolector_free_array_assignment (
        Btor * btor, char ** indices, char ** values, uint32_t size) \
      except +raise_py_error

    void boolector_uf_assignment (Btor * btor,
                                  BoolectorNode * n_array,
                                  char *** args,
                                  char *** values,
                                  uint32_t * size) \
      except +raise_py_error

    void boolector_free_uf_assignment (
        Btor * btor, char ** args, char ** values, uint32_t size) \
      except +raise_py_error

    void boolector_print_model (Btor * btor, char * format, FILE * file) \
      except +raise_py_error

    BoolectorSort boolector_bool_sort (Btor * btor) \
      except +raise_py_error

    BoolectorSort boolector_bitvec_sort (Btor * btor, uint32_t width) \
      except +raise_py_error

    BoolectorSort boolector_array_sort (Btor * btor,
                                        BoolectorSort index,
                                        BoolectorSort elem) \
      except +raise_py_error

    BoolectorSort boolector_fun_sort (Btor * btor,
                                      BoolectorSort * domain,
                                      uint32_t arity,
                                      BoolectorSort codomain) \
      except +raise_py_error

    void boolector_release_sort (Btor * btor, BoolectorSort sort) \
      except +raise_py_error

    int32_t boolector_parse (Btor * btor,
                             FILE * infile,
                             const char * infile_name,
                             FILE * outfile,
                             char ** error_msg,
                             int32_t * status) \
      except +raise_py_error

    #int32_t boolector_parse_btor (Btor * btor,
    #                              FILE * file,
    #                              const char * file_name,
    #                              char ** error_msg,
    #                              int32_t * status) \
    #  except +raise_py_error

    #int32_t boolector_parse_smt1 (Btor * btor,
    #                              FILE * file,
    #                              const char * file_name,
    #                              char ** error_msg,
    #                              int32_t * status) \
    #  except +raise_py_error

    #int32_t boolector_parse_smt2 (Btor * btor,
    #                              FILE * file,
    #                              const char * file_name,
    #                              char ** error_msg,
    #                              int32_t * status) \
    #  except +raise_py_error

    void boolector_dump_btor_node (Btor * btor, FILE * file,
                                   BoolectorNode * node) \
      except +raise_py_error

    void boolector_dump_btor (Btor * btor, FILE * file) \
      except +raise_py_error

    void boolector_dump_smt2_node (Btor * btor, FILE * file,
                                   BoolectorNode * node) \
      except +raise_py_error

    void boolector_dump_smt2 (Btor * btor, FILE * file) \
      except +raise_py_error

    void boolector_dump_aiger_ascii (Btor * btor, FILE * file,
                                     bool merge_roots) \
      except +raise_py_error

    void boolector_dump_aiger_binary (Btor * btor, FILE * file,bool merge_roots) \
      except +raise_py_error

    const char * boolector_copyright (Btor * btor) \
      except +raise_py_error

    const char * boolector_version (Btor * btor) \
      except +raise_py_error

    const char * boolector_git_id (Btor * btor) \
      except +raise_py_error
