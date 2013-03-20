#ifndef BTORIBV_H_INCLUDED
#define BTORIBV_H_INCLUDED

#include "IBitVector.h"

class BtorIBV : public IBitVector
{
  Btor *btor;

 public:
  BtorIBV (Btor *);
};

#endif
