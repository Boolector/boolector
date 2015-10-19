/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2014 Aina Niemetz.
 *  Copyright (C) 2015 Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORMSG_H_INCLUDED
#define BTORMSG_H_INCLUDED

#include <stdbool.h>
#include <string.h>
#include "utils/btormem.h"

#define BTOR_MSG(btormsg, level, msg...)        \
  do                                            \
  {                                             \
    if (*btormsg->verbosity < level) break;     \
    btor_msg (btormsg, false, __FILE__, ##msg); \
  } while (0)

typedef struct
{
  BtorMemMgr *mm;
  char *prefix;
  int *verbosity;
} BtorMsg;

BtorMsg *btor_new_btor_msg (BtorMemMgr *mm, int *verbosity);
void btor_delete_btor_msg (BtorMsg *msg);
void btor_msg (BtorMsg *msg, bool log, char *filename, char *fmt, ...);

#endif
