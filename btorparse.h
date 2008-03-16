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

struct BtorParseResult
{
  int nvars;
  BtorExp **vars;

  int nroots;
  BtorExp **roots;

  int nregs;
  BtorExp **regs;
  BtorExp **next;
};

struct BtorParserAPI
{
  BtorInitParser init;
  BtorResetParser reset;
  BtorParse parse;
};

#endif
