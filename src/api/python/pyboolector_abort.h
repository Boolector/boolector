/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2021 by the authors listed in the AUTHORS file.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef PYBOOLECTOR_ABORT_H_INCLUDED
#define PYBOOLECTOR_ABORT_H_INCLUDED

#if __cplusplus
extern "C" {
#endif

void pyboolector_abort_fun (const char* msg);

const char * pyboolector_get_err_msg (void);

#if __cplusplus
}
#endif
#endif
