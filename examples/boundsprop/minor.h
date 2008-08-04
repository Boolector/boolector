#ifndef MINOR_H_INCLUDED
#define MINOR_H_INCLUDED

#include "../../boolector.h"

BtorExp *btor_minor (Btor *btor,
                     BtorExp *a,
                     BtorExp *b,
                     BtorExp *c,
                     BtorExp *d,
                     BtorExp *m,
                     int num_bits);

#endif
