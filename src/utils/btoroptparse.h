#include "utils/btormem.h"
#include "utils/btorstack.h"

#include <stdbool.h>

/*------------------------------------------------------------------------*/

enum BtorReadArg
{
  BTOR_READ_ARG_NONE,
  BTOR_READ_ARG_NONE_VIA_EQ,
  BTOR_READ_ARG_STR,
  BTOR_READ_ARG_STR_VIA_EQ,
  BTOR_READ_ARG_INT,
  BTOR_READ_ARG_INT_VIA_EQ,
};
typedef enum BtorReadArg BtorReadArg;

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
  BtorReadArg readval; /* how did we read the passed option value? */
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
                          bool (*has_str_arg) (const char *));
