#ifndef BTOREXIT_H_INCLUDED
#define BTOREXIT_H_INCLUDED

enum BtorExitCode
{
  BTOR_SUCC_EXIT,
  BTOR_ERR_EXIT,
  BTOR_SAT_EXIT,
  BTOR_UNSAT_EXIT
};

typedef enum BtorExitCode BtorExitCode;

#endif
