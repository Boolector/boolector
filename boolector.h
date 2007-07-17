#ifndef BOOLECTOR_H_INCLUDED
#define BOOLECTOR_H_INCLUDED

#include <stdio.h>

/*------------------------------------------------------------------------*/
/* PUBLIC INTERFACE                                                       */
/*------------------------------------------------------------------------*/

/*------------------------------------------------------------------------*/
/* Declarations                                                           */
/*------------------------------------------------------------------------*/

typedef struct BtorExp BtorExp;

typedef struct BtorExpMgr BtorExpMgr;

/*------------------------------------------------------------------------*/
/* BtorExpMgr                                                             */
/*------------------------------------------------------------------------*/

BtorExpMgr *btor_new_exp_mgr (void);

void btor_delete_exp_mgr (BtorExpMgr *emgr);

/*------------------------------------------------------------------------*/
/* BtorExpression                                                         */
/*------------------------------------------------------------------------*/

/* constant */
BtorExp *btor_const_exp (BtorExpMgr *emgr, const char *bits);

/* variables are sticky and cannot be deleted */
BtorExp *btor_var_exp (BtorExpMgr *emgr, int len, const char *symbol);

/* arrays are sticky and cannot be deleted */
BtorExp *btor_array_exp (BtorExpMgr *emgr,
                         int elem_len,
                         int index_len,
                         const char *symbol);

BtorExp *btor_not_exp (BtorExpMgr *emgr, BtorExp *exp);

/* Two's complement */
BtorExp *btor_neg_exp (BtorExpMgr *emgr, BtorExp *exp);

BtorExp *btor_nego_exp (BtorExpMgr *emgr, BtorExp *exp);

BtorExp *btor_redor_exp (BtorExpMgr *emgr, BtorExp *exp);

BtorExp *btor_redxor_exp (BtorExpMgr *emgr, BtorExp *exp);

BtorExp *btor_redand_exp (BtorExpMgr *emgr, BtorExp *exp);

BtorExp *btor_slice_exp (BtorExpMgr *emgr, BtorExp *exp, int upper, int lower);

BtorExp *btor_uext_exp (BtorExpMgr *emgr, BtorExp *exp, int len);

BtorExp *btor_sext_exp (BtorExpMgr *emgr, BtorExp *exp, int len);

BtorExp *btor_or_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

BtorExp *btor_xor_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

BtorExp *btor_xnor_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

BtorExp *btor_and_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

BtorExp *btor_eq_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

BtorExp *btor_ne_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

/* For unsigned and signed */
BtorExp *btor_add_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

BtorExp *btor_uaddo_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

BtorExp *btor_saddo_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

BtorExp *btor_umul_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

BtorExp *btor_umulo_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

BtorExp *btor_smul_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

BtorExp *btor_smulo_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

BtorExp *btor_ult_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

BtorExp *btor_slt_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

BtorExp *btor_ulte_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

BtorExp *btor_slte_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

BtorExp *btor_ugt_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

BtorExp *btor_sgt_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

BtorExp *btor_ugte_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

BtorExp *btor_sgte_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

BtorExp *btor_sll_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

BtorExp *btor_srl_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

BtorExp *btor_sra_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

BtorExp *btor_rol_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

BtorExp *btor_ror_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

/* For unsigned and signed */
BtorExp *btor_sub_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

BtorExp *btor_usubo_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

BtorExp *btor_ssubo_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

BtorExp *btor_udiv_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

BtorExp *btor_sdiv_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

BtorExp *btor_sdivo_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

BtorExp *btor_umod_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

BtorExp *btor_smod_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

BtorExp *btor_concat_exp (BtorExpMgr *emgr, BtorExp *e1, BtorExp *e2);

BtorExp *btor_acc_exp (BtorExpMgr *emgr, BtorExp *e_array, BtorExp *e_index);

BtorExp *btor_cond_exp (BtorExpMgr *emgr,
                        BtorExp *e_cond,
                        BtorExp *e_if,
                        BtorExp *e_else);

int btor_get_exp_len (BtorExpMgr *emgr, BtorExp *exp);

int btor_is_array_exp (BtorExpMgr *emgr, BtorExp *exp);

int btor_get_index_exp_len (BtorExpMgr *emgr, BtorExp *e_array);

/* for variablese and arrays only */
char *btor_get_symbol_exp (BtorExpMgr *emgr, BtorExp *exp);

BtorExp *btor_copy_exp (BtorExpMgr *emgr, BtorExp *exp);

void btor_release_exp (BtorExpMgr *emgr, BtorExp *exp);

void btor_dump_exp (BtorExpMgr *emgr, FILE *file, BtorExp *exp);

int btor_sat_exp (BtorExpMgr *emgr, BtorExp *exp);

char *btor_get_assignment_var_exp (BtorExpMgr *emgr, BtorExp *exp);

char *btor_get_assignment_array_exp (BtorExpMgr *emgr,
                                     BtorExp *e_array,
                                     int pos);

#endif
