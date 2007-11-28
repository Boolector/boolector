#ifndef BTOREXIT_H_INCLUDED
#define BTOREXIT_H_INCLUDED

enum BtorExitCode
{
  BTOR_SUCC_EXIT    = 0,
  BTOR_ERR_EXIT     = 1,
  BTOR_SAT_EXIT     = 2,
  BTOR_UNSAT_EXIT   = 3,
  BTOR_UNKNOWN_EXIT = 4
};

typedef enum BtorExitCode BtorExitCode;

#endif
