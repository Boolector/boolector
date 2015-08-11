/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2014 Armin Biere.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORCONST_H_INCLUDED
#define BTORCONST_H_INCLUDED

#include <stdint.h>
#include "utils/btormem.h"

/*------------------------------------------------------------------------*/

enum BtorSpecialConst
{
  BTOR_SPECIAL_CONST_ZERO,
  BTOR_SPECIAL_CONST_ONE,
  BTOR_SPECIAL_CONST_ONES,
  BTOR_SPECIAL_CONST_ONE_ONES,
  BTOR_SPECIAL_CONST_NONE
};

typedef enum BtorSpecialConst BtorSpecialConst;

/*------------------------------------------------------------------------*/

char *btor_zero_const (BtorMemMgr *mm, uint32_t len);

char *btor_one_const (BtorMemMgr *mm, uint32_t len);

char *btor_ones_const (BtorMemMgr *mm, uint32_t len);

char *btor_int_to_const (BtorMemMgr *mm, int x, uint32_t len);

char *btor_unsigned_to_const (BtorMemMgr *mm, unsigned x, uint32_t len);

char *btor_decimal_to_const (BtorMemMgr *mm, const char *str);

char *btor_decimal_to_const_n (BtorMemMgr *mm, const char *str, uint32_t len);

char *btor_hex_to_const (BtorMemMgr *mm, const char *str);

char *btor_hex_to_const_n (BtorMemMgr *mm, const char *str, uint32_t len);

int btor_is_zero_const (const char *str);

int btor_is_one_const (const char *str);

int btor_is_ones_const (const char *str);

int btor_is_small_positive_int_const (const char *str);

int btor_is_power_of_two_const (const char *str);

int btor_is_zero_or_ones_const (const char *str);

BtorSpecialConst btor_is_special_const (const char *str);

/*------------------------------------------------------------------------*/
/* Fixed width operators.  The arguments and the result have the same width.
 */

void btor_invert_const (BtorMemMgr *mm, char *a);

char *btor_not_const (BtorMemMgr *mm, const char *a);

char *btor_and_const (BtorMemMgr *mm, const char *a, const char *b);

char *btor_eq_const (BtorMemMgr *mm, const char *a, const char *b);

char *btor_ult_const (BtorMemMgr *mm, const char *a, const char *b);

char *btor_add_const (BtorMemMgr *mm, const char *a, const char *b);

char *btor_neg_const (BtorMemMgr *mm, const char *a);

char *btor_sub_const (BtorMemMgr *mm, const char *a, const char *b);

char *btor_mul_const (BtorMemMgr *mm, const char *a, const char *b);

char *btor_udiv_const (BtorMemMgr *mm, const char *a, const char *b);

char *btor_urem_const (BtorMemMgr *mm, const char *a, const char *b);

char *btor_sll_const (BtorMemMgr *mm, const char *a, const char *b);

char *btor_srl_const (BtorMemMgr *mm, const char *a, const char *b);

char *btor_uext_const (BtorMemMgr *mm, const char *c, uint32_t len);

char *btor_concat_const (BtorMemMgr *mm, const char *a, const char *b);

char *btor_inverse_const (BtorMemMgr *mm, const char *a);

/*------------------------------------------------------------------------*/
/* Three valued logic.
 */
char *btor_x_const_3vl (BtorMemMgr *mm, uint32_t len);

char *btor_not_const_3vl (BtorMemMgr *mm, const char *a);

char *btor_eq_const_3vl (BtorMemMgr *mm, const char *a, const char *b);

int btor_is_const_2vl (BtorMemMgr *mm, const char *c);

char *btor_ground_const_3vl (BtorMemMgr *mm, const char *c);

/*------------------------------------------------------------------------*/
/* Work for both fixed and unbounded bit width constants.
 */
char *btor_copy_const (BtorMemMgr *mm, const char *c);

void btor_delete_const (BtorMemMgr *mm, char *c);

int btor_get_num_leading_zeros_const (BtorMemMgr *mm, const char *c);

int btor_get_num_leading_ones_const (BtorMemMgr *mm, const char *c);

char *btor_slice_const (BtorMemMgr *mm,
                        const char *a,
                        uint32_t upper,
                        uint32_t lower);

/*------------------------------------------------------------------------*/
/* Output functions.
 */
char *btor_const_to_hex (BtorMemMgr *mm, const char *c);

char *btor_const_to_decimal (BtorMemMgr *mm, const char *c);

#endif
