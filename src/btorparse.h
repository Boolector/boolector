/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2012 Armin Biere.
 *  Copyright (C) 2013-2015 Mathias Preiner.
 *  Copyright (C) 2015-2018 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORPARSE_H_INCLUDED
#define BTORPARSE_H_INCLUDED

#include "boolector.h"
#include "btorlogic.h"
#include "btormsg.h"
#include "utils/btorstack.h"

#include <stdio.h>

/*------------------------------------------------------------------------*/

typedef struct BtorParser BtorParser;
typedef struct BtorParseResult BtorParseResult;
typedef struct BtorParserAPI BtorParserAPI;

typedef BtorParser *(*BtorInitParser) (Btor *);

typedef void (*BtorResetParser) (void *);

typedef char *(*BtorParse) (BtorParser *,
                            BtorCharStack *prefix,
                            FILE *,
                            const char *,
                            FILE *,
                            BtorParseResult *);

struct BtorParseResult
{
  BtorLogic logic;
  int32_t status;
  int32_t result;
  uint32_t nsatcalls;
};

struct BtorParserAPI
{
  BtorInitParser init;
  BtorResetParser reset;
  BtorParse parse;
};

int32_t btor_parse (Btor *btor,
                    FILE *infile,
                    const char *infile_name,
                    FILE *outfile,
                    char **error_msg,
                    int32_t *status);

int32_t btor_parse_btor (Btor *btor,
                         FILE *infile,
                         const char *infile_name,
                         FILE *outfile,
                         char **error_msg,
                         int32_t *status);

int32_t btor_parse_btor2 (Btor *btor,
                          FILE *infile,
                          const char *infile_name,
                          FILE *outfile,
                          char **error_msg,
                          int32_t *status);

int32_t btor_parse_smt1 (Btor *btor,
                         FILE *infile,
                         const char *infile_name,
                         FILE *outfile,
                         char **error_msg,
                         int32_t *status);

int32_t btor_parse_smt2 (Btor *btor,
                         FILE *infile,
                         const char *infile_name,
                         FILE *outfile,
                         char **error_msg,
                         int32_t *status);

BtorMsg *boolector_get_btor_msg (Btor *btor);
#endif
