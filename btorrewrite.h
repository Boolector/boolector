#ifndef BTORREWRITE_H_INCLUDED
#define BTORREWRITE_H_INCLUDED

#include "btorexp.h"

/*------------------------------------------------------------------------*/
/* PRIVATE INTERFACE                                                      */
/*------------------------------------------------------------------------*/

BtorExp *btor_rewrite_slice_exp (Btor *btor,
                                 BtorExp *exp,
                                 int upper,
                                 int lower);

BtorExp *btor_rewrite_and_exp (Btor *btor, BtorExp *e0, BtorExp *e1);

BtorExp *btor_rewrite_eq_exp (Btor *btor, BtorExp *e0, BtorExp *e1);

BtorExp *btor_rewrite_add_exp (Btor *btor, BtorExp *e0, BtorExp *e1);

BtorExp *btor_rewrite_mul_exp (Btor *btor, BtorExp *e0, BtorExp *e1);

BtorExp *btor_rewrite_ult_exp (Btor *btor, BtorExp *e0, BtorExp *e1);

BtorExp *btor_rewrite_sll_exp (Btor *btor, BtorExp *e0, BtorExp *e1);

BtorExp *btor_rewrite_srl_exp (Btor *btor, BtorExp *e0, BtorExp *e1);

BtorExp *btor_rewrite_udiv_exp (Btor *btor, BtorExp *e0, BtorExp *e1);

BtorExp *btor_rewrite_urem_exp (Btor *btor, BtorExp *e0, BtorExp *e1);

BtorExp *btor_rewrite_concat_exp (Btor *btor, BtorExp *e0, BtorExp *e1);

BtorExp *btor_rewrite_read_exp (Btor *btor, BtorExp *e_array, BtorExp *e_index);

BtorExp *btor_rewrite_write_exp (Btor *btor,
                                 BtorExp *e_array,
                                 BtorExp *e_index,
                                 BtorExp *e_value);

BtorExp *btor_rewrite_cond_exp (Btor *btor,
                                BtorExp *e_cond,
                                BtorExp *e_if,
                                BtorExp *e_else);

#endif
