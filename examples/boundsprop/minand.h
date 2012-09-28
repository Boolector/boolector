#ifndef MINAND_H_INCLUDED
#define MINAND_H_INCLUDED

#include "../../boolector.h"

BtorNode *btor_minand (Btor *btor,
                       BtorNode *a_in,
                       BtorNode *b_in,
                       BtorNode *c_in,
                       BtorNode *d_in,
                       BtorNode *m_in,
                       int num_bits);

#endif
