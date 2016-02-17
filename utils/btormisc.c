/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2013 Armin Biere.
 *  Copyright (C) 2012-2014 Aina Niemetz.
 *  Copyright (C) 2012-2015 Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "utils/btormisc.h"
#include "btorcore.h"
#include "dumper/btordumpbtor.h"
#include "utils/btorutil.h"

#define BUFFER_SIZE 256
#define BUFCONCAT(BUF, CLEN, NLEN, ARGS...) \
  if (NLEN < BUFFER_SIZE - 1)               \
  {                                         \
    assert (strlen (BUF) == CLEN);          \
    sprintf (BUF + CLEN, ##ARGS);           \
    CLEN = NLEN;                            \
    assert (strlen (BUF) == CLEN);          \
  }                                         \
  else                                      \
  {                                         \
    return "buffer exceeded";               \
  }

char g_strbuf[BUFFER_SIZE];
int g_strbufpos = 0;

char *
node2string (BtorNode *exp)
{
  Btor *btor;
  BtorNode *real_exp;
  const char *name, *tmp;
  char strbuf[BUFFER_SIZE], *bufstart;
  size_t cur_len, new_len;
  int i;

  if (!exp) return "0";

  real_exp = BTOR_REAL_ADDR_NODE (exp);
  btor     = real_exp->btor;
  name     = g_btor_op2str[real_exp->kind];

  strbuf[0] = '\0';
  cur_len   = 0;
  new_len   = btor_num_digits_util (real_exp->id);
  if (BTOR_IS_INVERTED_NODE (exp)) new_len += 1;
  new_len += 1 + strlen (name); /* space + name */
  BUFCONCAT (strbuf, cur_len, new_len, "%d %s", BTOR_GET_ID_NODE (exp), name);

  for (i = 0; i < real_exp->arity; i++)
  {
    new_len += 1; /* space */
    new_len += btor_num_digits_util (BTOR_REAL_ADDR_NODE (real_exp->e[i])->id);
    if (BTOR_IS_INVERTED_NODE (real_exp->e[i])) new_len += 1;
    BUFCONCAT (
        strbuf, cur_len, new_len, " %d", BTOR_GET_ID_NODE (real_exp->e[i]));
  }

  if (BTOR_IS_SLICE_NODE (real_exp))
  {
    new_len += btor_num_digits_util (btor_slice_get_upper (exp));
    new_len += btor_num_digits_util (btor_slice_get_lower (exp));
    new_len += 2;
    BUFCONCAT (strbuf,
               cur_len,
               new_len,
               " %d %d",
               btor_slice_get_upper (exp),
               btor_slice_get_lower (exp));
  }
  else if ((BTOR_IS_BV_VAR_NODE (real_exp) || BTOR_IS_UF_NODE (real_exp)
            || BTOR_IS_PARAM_NODE (real_exp))
           && (tmp = btor_get_symbol_exp (btor, real_exp)))
  {
    new_len += strlen (tmp);
    new_len += 1;
    BUFCONCAT (strbuf, cur_len, new_len, " %s", tmp);
  }
  // FIXME: len exceeds buf
  //  else if (BTOR_IS_BV_CONST_NODE (exp))
  //    sprintf (strbuf, "%s %s", strbuf, exp->bits);

  assert (cur_len == strlen (strbuf));
  if (g_strbufpos + cur_len + 1 > BUFFER_SIZE - 1) g_strbufpos = 0;

  bufstart = g_strbuf + g_strbufpos;
  sprintf (bufstart, "%s", strbuf);
  g_strbufpos += cur_len + 1;

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
