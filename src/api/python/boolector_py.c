/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2021 by the authors listed in the AUTHORS file.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */
#include "boolector_py.h"
#include "btorabort.h"
#include "btorcore.h"

static int32_t
py_terminate_btor (void *btor)
{
  assert (btor);

  PyObject *res;
  PyGILState_STATE gstate;
  Btor *bt;

  gstate = PyGILState_Ensure ();
  bt     = (Btor *) btor;
  if (!bt->cbs.term.fun) return 0;
  if (bt->cbs.term.done) return 1;
  res = PyObject_CallObject ((PyObject *) bt->cbs.term.fun,
                             (PyObject *) bt->cbs.term.state);
  if (PyErr_Occurred ()) PyErr_Print ();
  BTOR_ABORT (!res, "call to callback termination function failed");
  BTOR_ABORT (!PyBool_Check (res),
              "expected Boolean result for termination callback");
  if (res == Py_True)
    bt->cbs.term.done = 1;
  else
    bt->cbs.term.done = 0;
  Py_DECREF (res);
  PyGILState_Release (gstate);
  return bt->cbs.term.done;
}

void
boolector_py_set_term (Btor *btor, PyObject *fun, PyObject *state)
{
  BTOR_ABORT_ARG_NULL (btor);
  BTOR_ABORT_ARG_NULL (fun);

  Py_ssize_t i, size;
  PyObject *t, *tmp;
  BtorSATMgr *smgr;

  BTOR_ABORT (!PyCallable_Check (fun),
              "termination callback parameter is not callable");
  btor->cbs.term.termfun = py_terminate_btor;

  Py_XINCREF (fun);       /* inc ref to new callback */
  if (btor->cbs.term.fun) /* dec ref to prev callback */
    Py_XDECREF ((PyObject *) btor->cbs.term.fun);
  btor->cbs.term.fun = fun;

  if (btor->cbs.term.state) /* dec ref to prev state */
    Py_XDECREF ((PyObject *) btor->cbs.term.state);

  if (PyObject_TypeCheck (state, &PyTuple_Type))
  {
    Py_XINCREF (state);
    btor->cbs.term.state = state;
  }
  else if (PyObject_TypeCheck (state, &PyList_Type))
  {
    size = PyList_Size (state);
    tmp  = PyTuple_New (size);
    for (i = 0; i < size; i++)
    {
      t = PyList_GetItem (state, i);
      Py_XINCREF (t);
      PyTuple_SetItem (tmp, i, t);
    }
    btor->cbs.term.state = tmp;
  }
  else
  {
    Py_XINCREF (state);
    tmp = PyTuple_New (1);
    PyTuple_SetItem (tmp, 0, state);
    btor->cbs.term.state = tmp;
  }

  smgr = btor_get_sat_mgr (btor);
  btor_sat_mgr_set_term (smgr, py_terminate_btor, btor);
}

void
boolector_py_delete (Btor *btor)
{
  BTOR_ABORT_ARG_NULL (btor);
  if (btor->cbs.term.fun) Py_XDECREF (btor->cbs.term.fun);
  if (btor->cbs.term.state) Py_XDECREF (btor->cbs.term.state);
  boolector_delete (btor);
}
