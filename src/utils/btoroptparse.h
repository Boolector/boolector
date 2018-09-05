/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2016-2018 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTOROPTPARSE_H_INCLUDED
#define BTOROPTPARSE_H_INCLUDED

#include "btoropt.h"
#include "utils/btormem.h"
#include "utils/btorstack.h"

#include <stdbool.h>

/*------------------------------------------------------------------------*/

enum BtorArgRead
{
  BTOR_ARG_READ_NONE,
  BTOR_ARG_READ_NONE_VIA_EQ,
  BTOR_ARG_READ_STR,
  BTOR_ARG_READ_STR_VIA_EQ,
  BTOR_ARG_READ_INT,
  BTOR_ARG_READ_INT_VIA_EQ,
};
typedef enum BtorArgRead BtorArgRead;

enum BtorArgExpected
{
  BTOR_ARG_EXPECT_NONE,
  BTOR_ARG_EXPECT_INT,
  BTOR_ARG_EXPECT_STR,
};
typedef enum BtorArgExpected BtorArgExpected;

/*------------------------------------------------------------------------*/

#define BTOR_ARG_READ_NO_VALUE(val) \
  (val == BTOR_ARG_READ_NONE || val == BTOR_ARG_READ_NONE_VIA_EQ)

#define BTOR_ARG_READ_IS_INT(val) \
  (val == BTOR_ARG_READ_INT || val == BTOR_ARG_READ_INT_VIA_EQ)

#define BTOR_ARG_IS_UNEXPECTED(arg, readval, isdisable)                       \
  ((arg == BTOR_ARG_EXPECT_NONE || (arg == BTOR_ARG_EXPECT_INT && isdisable)) \
   && (readval == BTOR_ARG_READ_STR_VIA_EQ                                    \
       || readval == BTOR_ARG_READ_INT_VIA_EQ                                 \
       || readval == BTOR_ARG_READ_INT))

#define BTOR_ARG_IS_MISSING(arg, candisable, readval)               \
  ((arg == BTOR_ARG_EXPECT_STR && BTOR_ARG_READ_NO_VALUE (readval)) \
   || (arg == BTOR_ARG_EXPECT_INT                                   \
       && (((!candisable                                            \
             && (BTOR_ARG_READ_NO_VALUE (readval)                   \
                 || !BTOR_ARG_READ_IS_INT (readval))))              \
           || (readval == BTOR_ARG_READ_NONE_VIA_EQ))))

#define BTOR_ARG_IS_INVALID(arg, candisable, readval) \
  (arg == BTOR_ARG_EXPECT_INT && readval == BTOR_ARG_READ_STR_VIA_EQ)

/*------------------------------------------------------------------------*/

struct BtorParsedOpt
{
  BtorMemMgr *mm;
  BtorCharStack orig;  /* original option string without argument */
  BtorCharStack name;  /* option name */
  uint32_t val;        /* option value (0 if not given) */
  char *valstr;        /* original option value string (0 if not given) */
  bool isshrt;         /* is short option? */
  bool isdisable;      /* is --no-* option? (disabling option) */
  BtorArgRead readval; /* how did we read the passed option value? */
};
typedef struct BtorParsedOpt BtorParsedOpt;

BTOR_DECLARE_STACK (BtorParsedOptPtr, BtorParsedOpt *);

struct BtorParsedInput
{
  BtorMemMgr *mm;
  char *name;
};
typedef struct BtorParsedInput BtorParsedInput;

BTOR_DECLARE_STACK (BtorParsedInputPtr, BtorParsedInput *);

/*------------------------------------------------------------------------*/

void btor_optparse_parse (BtorMemMgr *mm,
                          int32_t argc,
                          char **argv,
                          BtorParsedOptPtrStack *opts,
                          BtorParsedInputPtrStack *infiles,
                          BtorOpt *btor_options,
                          bool (*has_str_arg) (const char *, BtorOpt *));

#endif
