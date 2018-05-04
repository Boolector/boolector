/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2014-2017 Aina Niemetz.
 *  Copyright (C) 2015 Mathias Preiner.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORMSG_H_INCLUDED
#define BTORMSG_H_INCLUDED

#include <stdbool.h>
#include <stdint.h>
#include <string.h>
#include "btoropt.h"
#include "btortypes.h"
#include "utils/btormem.h"

#define BTOR_MSG(btormsg, level, msg...)                                   \
  do                                                                       \
  {                                                                        \
    if (level && btor_opt_get (btormsg->btor, BTOR_OPT_VERBOSITY) < level) \
      break;                                                               \
    btor_msg (btormsg, false, __FILE__, ##msg);                            \
  } while (0)

typedef struct
{
  Btor *btor;
  char *prefix;
} BtorMsg;

BtorMsg *btor_msg_new (Btor *btor);

void btor_msg_delete (BtorMsg *msg);

void btor_msg (
    BtorMsg *msg, bool log, const char *filename, const char *fmt, ...);

#endif
