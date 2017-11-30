/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2015 Armin Biere.
 *  Copyright (C) 2012-2017 Aina Niemetz.
 *  Copyright (C) 2012-2015 Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORUTIL_H_INCLUDED
#define BTORUTIL_H_INCLUDED

#include "btortypes.h"
#include "utils/btormem.h"

#include <ctype.h>
#include <stdbool.h>
#include <stdint.h>

/*------------------------------------------------------------------------*/

#define BTOR_HAVE_GETRUSAGE  // TODO make this a configuration option

#define BTOR_MAX_UTIL(x, y) ((x) > (y) ? (x) : (y))

#define BTOR_MIN_UTIL(x, y) ((x) < (y) ? (x) : (y))

#define BTOR_AVERAGE_UTIL(a, b) ((b) ? ((double) (a)) / ((double) (b)) : 0.0)

#define BTOR_SWAP(TYPE, A, B)           \
  do                                    \
  {                                     \
    TYPE BTOR_SWAP_TMP = (A);           \
    (A)                = (B);           \
    (B)                = BTOR_SWAP_TMP; \
  } while (0)

/*------------------------------------------------------------------------*/

bool btor_util_is_power_of_2 (uint32_t x);

uint32_t btor_util_log_2 (uint32_t x);

int32_t btor_util_pow_2 (int32_t x);

int32_t btor_util_next_power_of_2 (int32_t x);

/*------------------------------------------------------------------------*/

uint32_t btor_util_num_digits (uint32_t x);

/*------------------------------------------------------------------------*/

char *btor_util_dec_to_bin_str (BtorMemMgr *mm, const char *str);

char *btor_util_dec_to_bin_str_n (BtorMemMgr *mm,
                                  const char *str,
                                  uint32_t len);

char *btor_util_hex_to_bin_str (BtorMemMgr *mm, const char *str);

char *btor_util_hex_to_bin_str_n (BtorMemMgr *mm,
                                  const char *str,
                                  uint32_t len);

/*------------------------------------------------------------------------*/

#ifdef BTOR_HAVE_GETRUSAGE
double btor_util_time_stamp (void);
double btor_util_process_time_thread (void);
#endif

double btor_util_current_time (void);

/*------------------------------------------------------------------------*/

int32_t btor_util_file_exists (const char *);
bool btor_util_file_has_suffix (const char *path, const char *suffix);

/*------------------------------------------------------------------------*/

char *btor_util_node2string (BtorNode *);
int32_t btor_util_vis_exp (Btor *btor, BtorNode *exp);

/*------------------------------------------------------------------------*/

char *btor_util_getenv_value (const char *name);

/*------------------------------------------------------------------------*/

#endif
