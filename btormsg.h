/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2014 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORMSG_H_INCLUDED
#define BTORMSG_H_INCLUDED

#include <string.h>
#include "utils/btormem.h"

#define BTOR_MSG(btormsg, level, msg...)        \
  do                                            \
  {                                             \
    btor_msg (btormsg, __FILE__, level, ##msg); \
  } while (0)

typedef struct
{
  BtorMemMgr *mm;
  char *prefix;
  int *verbosity;
} BtorMsg;

BtorMsg *btor_new_btor_msg (BtorMemMgr *mm, int *verbosity);
void btor_delete_btor_msg (BtorMsg *msg);
void btor_msg (BtorMsg *msg, char *filename, int level, char *fmt, ...);

#endif
