/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2012 Armin Biere.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORLOGIC_H_INCLUDED
#define BTORLOGIC_H_INCLUDED

enum BtorLogic
{
  BTOR_LOGIC_BV,
  BTOR_LOGIC_QF_ABV,
  BTOR_LOGIC_QF_AUFBV,
  BTOR_LOGIC_QF_BV,
  BTOR_LOGIC_QF_UFBV,
  BTOR_LOGIC_ALL,
};

typedef enum BtorLogic BtorLogic;

#endif
