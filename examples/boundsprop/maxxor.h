#ifndef MAXXOR_H_INCLUDED
#define MAXXOR_H_INCLUDED

#include "../../boolector.h"

BtorNode *btor_maxxor (Btor *btor,
                       BtorNode *a_in,
                       BtorNode *b_in,
                       BtorNode *c_in,
                       BtorNode *d_in,
                       BtorNode *m_in,
                       int num_bits);

#endif
