/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2013 Armin Biere.
 *  Copyright (C) 2012-2017 Aina Niemetz.
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

#define BUFFER_SIZE 1024
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
  char strbuf[BUFFER_SIZE], *bufstart, *bits;
  size_t cur_len, new_len;
  int i;

  if (!exp) return "0";

  real_exp = BTOR_REAL_ADDR_NODE (exp);
  btor     = real_exp->btor;
  name     = g_btor_op2str[real_exp->kind];

  strbuf[0] = '\0';
  cur_len   = 0;
  new_len   = btor_util_num_digits (real_exp->id);

  if (BTOR_IS_INVERTED_NODE (exp)) new_len += 1;
  new_len += 1 + strlen (name); /* space + name */
  BUFCONCAT (strbuf, cur_len, new_len, "%d %s", btor_exp_get_id (exp), name);

  for (i = 0; i < real_exp->arity; i++)
  {
    new_len += 1; /* space */
    new_len += btor_util_num_digits (BTOR_REAL_ADDR_NODE (real_exp->e[i])->id);
    if (BTOR_IS_INVERTED_NODE (real_exp->e[i])) new_len += 1;
    BUFCONCAT (
        strbuf, cur_len, new_len, " %d", btor_exp_get_id (real_exp->e[i]));
  }

  if (btor_is_slice_node (real_exp))
  {
    new_len += btor_util_num_digits (btor_slice_get_upper (exp)) + 1;
    new_len += btor_util_num_digits (btor_slice_get_lower (exp)) + 1;
    BUFCONCAT (strbuf,
               cur_len,
               new_len,
               " %d %d",
               btor_slice_get_upper (exp),
               btor_slice_get_lower (exp));
  }
  else if ((btor_is_bv_var_node (real_exp) || btor_is_uf_node (real_exp)
            || btor_is_param_node (real_exp))
           && (tmp = btor_get_symbol_exp (btor, real_exp)))
  {
    new_len += strlen (tmp) + 1;
    BUFCONCAT (strbuf, cur_len, new_len, " %s", tmp);
  }
  else if (btor_is_bv_const_node (exp))
  {
    bits = btor_bv_to_char (btor->mm, btor_const_get_bits (real_exp));
    new_len += strlen (bits) + 1;
    BUFCONCAT (strbuf, cur_len, new_len, " %s", bits);
    btor_mem_freestr (btor->mm, bits);
  }

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
