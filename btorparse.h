/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2012 Armin Biere.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORPARSE_H_INCLUDED
#define BTORPARSE_H_INCLUDED

#include "boolector.h"
#include "btorlogic.h"
#include "btorstack.h"

#include <stdio.h>

/*------------------------------------------------------------------------*/

typedef struct BtorParseOpt BtorParseOpt;
typedef struct BtorParser BtorParser;
typedef struct BtorParseResult BtorParseResult;
typedef struct BtorParserAPI BtorParserAPI;

typedef BtorParser *(*BtorInitParser) (Btor *, BtorParseOpt *);

typedef void (*BtorResetParser) (void *);

typedef char *(*BtorParse) (BtorParser *,
                            BtorCharStack *prefix,
                            FILE *,
                            const char *,
                            BtorParseResult *);

enum BtorParseSATStatus
{
  BTOR_PARSE_SAT_STATUS_UNKNOWN,
  BTOR_PARSE_SAT_STATUS_SAT,
  BTOR_PARSE_SAT_STATUS_UNSAT
};

typedef enum BtorParseSATStatus BtorParseSATStatus;

enum BtorParseMode
{
  BTOR_PARSE_MODE_BASIC_INCREMENTAL        = 1,
  BTOR_PARSE_MODE_INCREMENTAL_BUT_CONTINUE = 2,
  BTOR_PARSE_MODE_INCREMENTAL_IN_DEPTH     = 8,
  BTOR_PARSE_MODE_INCREMENTAL_LOOK_AHEAD   = 16,
  BTOR_PARSE_MODE_INCREMENTAL_INTERVAL     = 32,
  BTOR_PARSE_MODE_INCREMENTAL_WINDOW       = (8 | 16 | 32),
};

typedef enum BtorParseMode BtorParseMode;

struct BtorParseOpt
{
  BtorParseMode incremental;
  int verbosity;
  int need_model;
  int window;
};

struct BtorParseResult
{
  BtorLogic logic;
  BtorParseSATStatus status;
  BtorParseSATStatus result;

  int ninputs;
  BoolectorNode **inputs;

  int noutputs;
  BoolectorNode **outputs;
};

struct BtorParserAPI
{
  BtorInitParser init;
  BtorResetParser reset;
  BtorParse parse;
};

#endif
