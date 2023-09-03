:orphan:

Module Index: pyboolector
=========================

.. autoclass:: pyboolector.Boolector
   :members:

   .. autoattribute:: UNKNOWN

     Value representing an 'unknown' result of a call to
     :func:`~pyboolector.Boolector.Sat`.

   .. autoattribute:: SAT

     Value representing a 'sat' result of a call to
     :func:`~pyboolector.Boolector.Sat`.

   .. autoattribute:: UNSAT

     Value representing an 'unsat' result of a call to
     :func:`~pyboolector.Boolector.Sat`.

   .. autoattribute:: PARSE_ERROR

     Value representing a 'parse error' result of a call to
     :func:`~pyboolector.Boolector.Sat`.

.. autoclass:: pyboolector.BoolectorNode
   :members:
   :exclude-members: btor

   .. attribute:: btor

      The Boolector instance this node is associated with.

.. automodule:: pyboolector
   :members:
   :exclude-members: Boolector, BoolectorNode
   :show-inheritance:
