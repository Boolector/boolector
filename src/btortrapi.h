/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2013-2018 Aina Niemetz.
 *  Copyright (C) 2013-2017 Mathias Preiner.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */
#ifndef BTORTRAPI_H_INCLUDED
#define BTORTRAPI_H_INCLUDED

#include "btorcore.h"
#include <stdio.h>

#define BTOR_TRAPI_NODE_FMT "n%d@%p "
#define BTOR_TRAPI_SORT_FMT "s%d@%p "

#define BTOR_TRAPI_NODE_ID(exp)                                               \
  (btor_node_is_inverted (exp) ? -btor_node_real_addr (exp)->id : (exp)->id), \
      btor_node_real_addr (exp)->btor

#define BTOR_TRAPI_PRINT(args...)    \
  do                                 \
  {                                  \
    if (!btor->apitrace) break;      \
    btor_trapi_print (btor, ##args); \
  } while (0)

#define BTOR_TRAPI(args...)                  \
  do                                         \
  {                                          \
    if (!btor->apitrace) break;              \
    btor_trapi (btor, __FUNCTION__, ##args); \
  } while (0)

#define BTOR_TRAPI_AUX(fun, args...) \
  do                                 \
  {                                  \
    if (!btor->apitrace) break;      \
    btor_trapi (btor, fun, ##args);  \
  } while (0)

#define BTOR_TRAPI_RETURN(args...) \
  do                               \
  {                                \
    if (!btor->apitrace) break;    \
    btor_trapi (btor, 0, ##args);  \
  } while (0)

#define BTOR_TRAPI_UNFUN_EXT(exp, fmt, args...) \
  BTOR_TRAPI (BTOR_TRAPI_NODE_FMT fmt, BTOR_TRAPI_NODE_ID (exp), ##args)

#define BTOR_TRAPI_UNFUN(exp) \
  BTOR_TRAPI (BTOR_TRAPI_NODE_FMT, BTOR_TRAPI_NODE_ID (exp))

#define BTOR_TRAPI_BINFUN(e0, e1)                      \
  BTOR_TRAPI (BTOR_TRAPI_NODE_FMT BTOR_TRAPI_NODE_FMT, \
              BTOR_TRAPI_NODE_ID (e0),                 \
              BTOR_TRAPI_NODE_ID (e1))

#define BTOR_TRAPI_TERFUN(e0, e1, e2)                                      \
  BTOR_TRAPI (BTOR_TRAPI_NODE_FMT BTOR_TRAPI_NODE_FMT BTOR_TRAPI_NODE_FMT, \
              BTOR_TRAPI_NODE_ID (e0),                                     \
              BTOR_TRAPI_NODE_ID (e1),                                     \
              BTOR_TRAPI_NODE_ID (e2))

#define BTOR_TRAPI_RETURN_NODE(res) \
  BTOR_TRAPI_RETURN (BTOR_TRAPI_NODE_FMT, BTOR_TRAPI_NODE_ID (res))

#define BTOR_TRAPI_RETURN_PTR(res) BTOR_TRAPI_RETURN ("%p", res)

#define BTOR_TRAPI_RETURN_STR(res) BTOR_TRAPI_RETURN ("%s", res)

#define BTOR_TRAPI_RETURN_INT(res) BTOR_TRAPI_RETURN ("%d", res)

#define BTOR_TRAPI_RETURN_UINT(res) BTOR_TRAPI_RETURN ("%u", res)

#define BTOR_TRAPI_RETURN_BOOL(res) \
  BTOR_TRAPI_RETURN ("%s", (res) ? "true" : "false")

#define BTOR_TRAPI_RETURN_SORT(sort) \
  BTOR_TRAPI_RETURN (BTOR_TRAPI_SORT_FMT, sort, btor)

void btor_trapi_print (Btor *btor, const char *msg, ...);

void btor_trapi (Btor* btor, const char* fname, const char* msg, ...);

void btor_trapi_open_trace (Btor* btor, const char* name);
#endif
