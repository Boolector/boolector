#ifndef BTORPARSE_H_INCLUDED
#define BTORPARSE_H_INCLUDED

#include "btorexp.h"

#include <stdio.h>

typedef struct BtorParser BtorParser;
typedef struct BtorParseResult BtorParseResult;
typedef struct BtorParserAPI BtorParserAPI;
typedef BtorParser *(*BtorInitParser) (Btor *, int verbosity);
typedef void (*BtorResetParser) (void *);

typedef char *(*BtorParse) (BtorParser *,
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

struct BtorParseResult
{
  BtorParseSATStatus status;

  int ninputs;
  BtorExp **inputs;

  int noutputs;
  BtorExp **outputs;

  int nregs;
  BtorExp **regs;
  BtorExp **nexts;
};

struct BtorParserAPI
{
  BtorInitParser init;
  BtorResetParser reset;
  BtorParse parse;
};

#endif
