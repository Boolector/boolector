#ifndef BTORFTOR_H_INCLUDED
#define BTORFTOR_H_INCLUDED

#include <stdio.h>

#include "btorexp.h"

/*------------------------------------------------------------------------*/
/* PRIVATE INTERFACE                                                      */
/*------------------------------------------------------------------------*/

typedef struct BtorFtor BtorFtor;

typedef struct BtorFtorResult BtorFtorResult;

struct BtorFtorResult
{
  BtorExp **vars;
  int nvars;

  BtorExp **arrays;
  int narrays;

  BtorExp **roots;
  int nroots;
};

BtorFtor *btor_new_ftor (BtorExpMgr *, int verbosity);

void btor_delete_ftor (BtorFtor *);

const char *btor_parse_ftor (BtorFtor *,
                             FILE *file,
                             const char *file_name,
                             BtorFtorResult *);

#endif
