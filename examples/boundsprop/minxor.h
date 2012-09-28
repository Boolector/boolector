#ifndef MINXOR_H_INCLUDED
#define MINXOR_H_INCLUDED

#include "../../boolector.h"

BtorNode *btor_minxor (Btor *btor,
                       BtorNode *a_in,
                       BtorNode *b_in,
                       BtorNode *c_in,
                       BtorNode *d_in,
                       BtorNode *m_in,
                       int num_bits);

#endif
