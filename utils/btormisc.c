/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2013 Armin Biere.
 *  Copyright (C) 2012-2014 Aina Niemetz, Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "utils/btormisc.h"
#include "btorcore.h"
#include "dumper/btordumpbtor.h"

char g_strbuf[256];
int g_strbufpos = 0;

char *
node2string (BtorNode *exp)
{
  const char *name;
  char strbuf[100], *bufstart;
  int len, i;

  if (!exp) return "0";

  exp = BTOR_REAL_ADDR_NODE (exp);

  switch (exp->kind)
  {
    case BTOR_INVALID_NODE: name = "invalid"; break;
    case BTOR_BV_CONST_NODE: name = "const"; break;
    case BTOR_BV_VAR_NODE: name = "var"; break;
    case BTOR_PARAM_NODE: name = "param"; break;
    case BTOR_UF_NODE: name = "uf"; break;
    case BTOR_SLICE_NODE: name = "slice"; break;
    case BTOR_AND_NODE: name = "and"; break;
    case BTOR_BEQ_NODE:
    case BTOR_FEQ_NODE: name = "eq"; break;
    case BTOR_ADD_NODE: name = "add"; break;
    case BTOR_MUL_NODE: name = "mul"; break;
    case BTOR_ULT_NODE: name = "ult"; break;
    case BTOR_SLL_NODE: name = "sll"; break;
    case BTOR_SRL_NODE: name = "srl"; break;
    case BTOR_UDIV_NODE: name = "udiv"; break;
    case BTOR_UREM_NODE: name = "urem"; break;
    case BTOR_CONCAT_NODE: name = "concat"; break;
    case BTOR_LAMBDA_NODE: name = "lambda"; break;
    case BTOR_BCOND_NODE: name = "bcond"; break;
    case BTOR_ARGS_NODE: name = "args"; break;
    case BTOR_APPLY_NODE: name = "apply"; break;
    case BTOR_PROXY_NODE: name = "proxy"; break;
    default: name = "unknown";
  }

  sprintf (strbuf, "%d %s", BTOR_GET_ID_NODE (exp), name);
  for (i = 0; i < exp->arity; i++)
  {
    sprintf (strbuf, "%s %d", strbuf, BTOR_GET_ID_NODE (exp->e[i]));
    if (strlen (strbuf) >= 100) break;
  }

  if (exp->kind == BTOR_SLICE_NODE)
    sprintf (strbuf, "%s %d %d", strbuf, exp->upper, exp->lower);
  // FIXME: len exceeds buf
  //  else if (BTOR_IS_BV_CONST_NODE (exp))
  //    sprintf (strbuf, "%s %s", strbuf, exp->bits);

  len = strlen (strbuf) + 1;

  if (g_strbufpos + len > 255) g_strbufpos = 0;

  bufstart = g_strbuf + g_strbufpos;
  sprintf (bufstart, "%s", strbuf);
  g_strbufpos += len;

  return bufstart;
}

int
btor_vis_exp (Btor *btor, BtorNode *exp)
{
  char cmd[100], *path;
  FILE *file;
  int res;
  sprintf (cmd, "btorvis ");
  path = cmd + strlen (cmd);
  sprintf (path, "/tmp/btorvisexp.%d.btor", btor->vis_idx++);
  file = fopen (path, "w");
  btor_dump_btor_node (btor, file, exp);
  fclose (file);
  strcat (cmd, "&");
  res = system (cmd);
  return res;
}

void
btor_print_bfs_path (Btor *btor, BtorNode *from, BtorNode *to)
{
  assert (from);
  assert (from->parent);
  assert (to);

  BtorNode *cur;

  cur = BTOR_REAL_ADDR_NODE (from);
  to  = BTOR_REAL_ADDR_NODE (to);

  printf ("%d path", btor->stats.lod_refinements);
  while (cur != to)
  {
    assert (BTOR_REAL_ADDR_NODE (cur->parent));
    printf (" %d", cur->id);
    cur = BTOR_REAL_ADDR_NODE (cur->parent);
  }
  printf (" %d\n", to->id);
}
