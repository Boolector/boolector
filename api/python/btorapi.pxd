from libc.stdio cimport FILE

cdef extern from "boolector.h":
      ctypedef struct BtorNode:
        pass
    #  ctypedef struct BtorSort:
    #    pass
      ctypedef struct Btor:
        pass

    #void boolector_set_trapi (Btor * btor, FILE * apitrace)
    #FILE *boolector_get_trapi (Btor * btor)

      Btor * boolector_new ()

      void boolector_delete (Btor * btor)

      # debug
    #  void boolector_print (Btor * btor, BtorNode * node)

      Btor *boolector_clone (Btor * btor)

      void boolector_enable_model_gen (Btor * btor)

      void boolector_generate_model_for_all_reads (Btor * btor)

      void boolector_enable_inc_usage (Btor * btor)

      int boolector_set_sat_solver (Btor * btor, const char * solver)

      void boolector_set_rewrite_level (Btor * btor, int rewrite_level)

      int boolector_get_refs (Btor * btor)

      void boolector_simplify (Btor * btor)

      void boolector_enable_beta_reduce_all (Btor * btor) 

      BtorNode *boolector_const (Btor * btor, const char * bits)

      BtorNode *boolector_zero (Btor * btor, int width)

      BtorNode *boolector_false (Btor * btor)

      BtorNode *boolector_ones (Btor * btor, int width)

      BtorNode *boolector_true (Btor * btor)

      BtorNode *boolector_one (Btor * btor, int width)

      BtorNode *boolector_unsigned_int (Btor * btor, unsigned u, int width)

      BtorNode *boolector_int (Btor * btor, int i, int width)

      BtorNode *boolector_var (Btor * btor, int width, const char *symbol)

      BtorNode *boolector_array (Btor * btor, int elem_width, int index_width,
                                 const char *symbol)

      BtorNode *boolector_not (Btor * btor, BtorNode * exp)

      BtorNode *boolector_neg (Btor * btor, BtorNode * exp)

      BtorNode *boolector_redor (Btor * btor, BtorNode * exp)

      BtorNode *boolector_redxor (Btor * btor, BtorNode * exp)

      BtorNode *boolector_redand (Btor * btor, BtorNode * exp)

      BtorNode *boolector_slice (Btor * btor, BtorNode * exp, int upper,
                                 int lower)

      BtorNode *boolector_uext (Btor * btor, BtorNode * exp, int width)

      BtorNode *boolector_sext (Btor * btor, BtorNode * exp, int width)

      BtorNode *boolector_implies (Btor * btor, BtorNode * e0, BtorNode * e1)

      BtorNode *boolector_iff (Btor * btor, BtorNode * e0, BtorNode * e1)

      BtorNode *boolector_xor (Btor * btor, BtorNode * e0, BtorNode * e1)

      BtorNode *boolector_xnor (Btor * btor, BtorNode * e0, BtorNode * e1)

      BtorNode *boolector_and (Btor * btor, BtorNode * e0, BtorNode * e1)

      BtorNode *boolector_nand (Btor * btor, BtorNode * e0, BtorNode * e1)

      BtorNode *boolector_or (Btor * btor, BtorNode * e0, BtorNode * e1)

      BtorNode *boolector_nor (Btor * btor, BtorNode * e0, BtorNode * e1)

      BtorNode *boolector_eq (Btor * btor, BtorNode * e0, BtorNode * e1)

      BtorNode *boolector_ne (Btor * btor, BtorNode * e0, BtorNode * e1)

      BtorNode *boolector_add (Btor * btor, BtorNode * e0, BtorNode * e1)

      BtorNode *boolector_uaddo (Btor * btor, BtorNode * e0, BtorNode * e1)

      BtorNode *boolector_saddo (Btor * btor, BtorNode * e0, BtorNode * e1)

      BtorNode *boolector_mul (Btor * btor, BtorNode * e0, BtorNode * e1)

      BtorNode *boolector_umulo (Btor * btor, BtorNode * e0, BtorNode * e1)

      BtorNode *boolector_smulo (Btor * btor, BtorNode * e0, BtorNode * e1)

      BtorNode *boolector_ult (Btor * btor, BtorNode * e0, BtorNode * e1)

      BtorNode *boolector_slt (Btor * btor, BtorNode * e0, BtorNode * e1)

      BtorNode *boolector_ulte (Btor * btor, BtorNode * e0, BtorNode * e1)

      BtorNode *boolector_slte (Btor * btor, BtorNode * e0, BtorNode * e1)

      BtorNode *boolector_ugt (Btor * btor, BtorNode * e0, BtorNode * e1)

      BtorNode *boolector_sgt (Btor * btor, BtorNode * e0, BtorNode * e1)

      BtorNode *boolector_ugte (Btor * btor, BtorNode * e0, BtorNode * e1)

      BtorNode *boolector_sgte (Btor * btor, BtorNode * e0, BtorNode * e1)

      BtorNode *boolector_sll (Btor * btor, BtorNode * e0, BtorNode * e1)

      BtorNode *boolector_srl (Btor * btor, BtorNode * e0, BtorNode * e1)

      BtorNode *boolector_sra (Btor * btor, BtorNode * e0, BtorNode * e1)

      BtorNode *boolector_rol (Btor * btor, BtorNode * e0, BtorNode * e1)

      BtorNode *boolector_ror (Btor * btor, BtorNode * e0, BtorNode * e1)

      BtorNode *boolector_sub (Btor * btor, BtorNode * e0, BtorNode * e1)

      BtorNode *boolector_usubo (Btor * btor, BtorNode * e0, BtorNode * e1)

      BtorNode *boolector_ssubo (Btor * btor, BtorNode * e0, BtorNode * e1)

      BtorNode *boolector_udiv (Btor * btor, BtorNode * e0, BtorNode * e1)

      BtorNode *boolector_sdiv (Btor * btor, BtorNode * e0, BtorNode * e1)

      BtorNode *boolector_sdivo (Btor * btor, BtorNode * e0, BtorNode * e1)

      BtorNode *boolector_urem (Btor * btor, BtorNode * e0, BtorNode * e1)

      BtorNode *boolector_srem (Btor * btor, BtorNode * e0, BtorNode * e1)

      BtorNode *boolector_smod (Btor * btor, BtorNode * e0, BtorNode * e1)

      BtorNode *boolector_concat (Btor * btor, BtorNode * e0, BtorNode * e1)

      BtorNode *boolector_read (Btor * btor, BtorNode * e_array,
                                BtorNode * e_index)

      BtorNode *boolector_write (Btor * btor, BtorNode * e_array,
                                 BtorNode * e_index, BtorNode * e_value)

      BtorNode *boolector_cond (Btor * btor, BtorNode * e_cond, BtorNode * e_if,
                                BtorNode * e_else)

    #  BtorNode *boolector_lambda (Btor * btor, BtorNode * param, BtorNode * exp)
    #
      BtorNode *boolector_param (Btor * btor, int width, const char * symbol) 

      BtorNode *boolector_fun (Btor * btor, int paramc, BtorNode ** params,
                               BtorNode * exp) 

      BtorNode *boolector_apply (Btor * btor, int argc, BtorNode ** args, 
                                 BtorNode * fun)

      BtorNode *boolector_inc (Btor * btor, BtorNode *exp)

      BtorNode *boolector_dec (Btor * btor, BtorNode *exp)

      int boolector_is_array (Btor * btor, BtorNode * exp)

      int boolector_is_fun (Btor * btor, BtorNode * exp)

      int boolector_get_fun_arity (Btor * btor, BtorNode * exp)

      int boolector_get_width (Btor * btor, BtorNode * exp)

      int boolector_get_index_width (Btor * btor, BtorNode * e_array)
    #
    #int boolector_fun_sort_check (Btor * btor, int argc, BtorNode ** args,
    #			      BtorNode * fun)
    #
      const char *boolector_get_symbol_of_var (Btor * btor, BtorNode * var)

      BtorNode *boolector_copy (Btor * btor, BtorNode * exp)

      void boolector_release (Btor * btor, BtorNode * exp)

      void boolector_dump_btor (Btor * btor, FILE * file, BtorNode * exp)

      void boolector_dump_btor_all (Btor * btor, FILE * file)

    #void boolector_dump_smt (Btor * btor, FILE * file, BtorNode * exp)
    #
    #void boolector_dump_smt2 (Btor * btor, FILE * file, BtorNode * exp)
    #
      void boolector_assert (Btor * btor, BtorNode * exp)

      void boolector_assume (Btor * btor, BtorNode * exp)

      int boolector_sat (Btor * btor)

      char *boolector_bv_assignment (Btor * btor, BtorNode * exp)

      void boolector_free_bv_assignment (Btor * btor, char * assignment)

      void boolector_array_assignment (Btor * btor, BtorNode * e_array,
                                       char ***indices, char ***values,
                                       int *size)

      void boolector_free_array_assignment (Btor * btor, char ** indices,
                                            char ** values, int size)
