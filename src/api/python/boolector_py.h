/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2021 by the authors listed in the AUTHORS file.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */
#ifndef BOOLECTOR_PY_H_INCLUDED
#define BOOLECTOR_PY_H_INCLUDED

#include <Python.h>
#include "boolector.h"

#if __cplusplus
extern "C" {
#endif

/*!
   Set a Python termination callback.

   :param btor:  Boolector instance.
   :param fun:   The termination callback Python function.
   :param state: The Python argument(s) to the termination callback function.

  .. note::
    This function is for Python API use only.
 */
void boolector_py_set_term (Btor* btor, PyObject* fun, PyObject* state);

/*!
  Delete a boolector instance (with possibly defined Python function
  callbacks) and free its resources.

  :param btor: Boolector instance.

  .. seealso::
    boolector_delete

  .. note::
    This function is for Python API use only.
*/
void boolector_py_delete (Btor* btor);

#if __cplusplus
}
#endif
#endif
