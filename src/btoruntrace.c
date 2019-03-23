/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2013 Christian Reisenberger.
 *  Copyright (C) 2013-2019 Aina Niemetz.
 *  Copyright (C) 2013-2018 Mathias Preiner.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include <assert.h>
#include <ctype.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include "boolector.h"
#include "btoropt.h"
#include "utils/btorhash.h"
#include "utils/btorhashptr.h"
#include "utils/btormem.h"
#include "utils/btorstack.h"
#include "utils/btorutil.h"

#ifdef BTOR_HAVE_SIGNALS
#include <signal.h>
#endif

/*------------------------------------------------------------------------*/

#define BTORUNT_USAGE                                                      \
  "usage: btoruntrace [ <option> ... ] [ <trace> ]\n"                      \
  "\n"                                                                     \
  "where <option> is one of the following:\n"                              \
  "\n"                                                                     \
  "  -v, --verbosity              increase verbosity\n"                    \
  "  -e, --exit-on-abort        exit on boolector abort\n"                 \
  "  -s, --skip-getters         skip 'getter' functions\n"                 \
  "  -i, --ignore-sat-result    do not exit on mismatching sat result\n"   \
  "  -b <btoropt> <val>         set boolector option <btoropt> to <val>\n" \
  "                             (Note: overrides trace opt settings!)\n"   \
  "  -d, --dump-stdout          dump to stdout "                           \
  "(default: dump to temp file at\n"                                       \
  "                             /tmp/<trace-basename>.(btor|smt2)\n"

/*------------------------------------------------------------------------*/

void boolector_chkclone (Btor *);
void boolector_set_btor_id (Btor *, BoolectorNode *, int32_t);
void boolector_get_btor_msg (Btor *);
void boolector_print_value_smt2 (Btor *, BoolectorNode *, char *, FILE *);

/*------------------------------------------------------------------------*/
typedef struct BtorUNT BtorUNT;

struct BtorUNTBtorOpt
{
  BtorOption kind;
  char *name;
  uint32_t val;
};

typedef struct BtorUNTBtorOpt BtorUNTBtorOpt;

BTOR_DECLARE_STACK (BtorUNTBtorOptPtr, BtorUNTBtorOpt *);

struct BtorUNT
{
  BtorMemMgr *mm;
  BtorUNTBtorOptPtrStack cl_btor_opts;
  BtorPtrHashTable *btor_opts;
  uint32_t verbosity;
  bool exit_on_abort;
  bool skip;
  bool ignore_sat;
  bool dump_stdout;
  uint32_t line;
  char *filename;
};

/*------------------------------------------------------------------------*/

static BtorUNT *
btorunt_new (void)
{
  BtorUNT *res;
  BtorMemMgr *mm;
  BtorUNTBtorOpt *opt;
  BtorOption o;
  Btor *tmpbtor;
  char *lng;
  uint32_t dflt;

  mm = btor_mem_mgr_new ();
  BTOR_CNEW (mm, res);
  res->mm = mm;
  BTOR_INIT_STACK (mm, res->cl_btor_opts);
  res->btor_opts = btor_hashptr_table_new (mm, btor_hash_str, btor_compare_str);
  tmpbtor        = boolector_new ();
  for (o = boolector_first_opt (tmpbtor), lng = 0;
       boolector_has_opt (tmpbtor, o);
       o = boolector_next_opt (tmpbtor, o))
  {
    lng  = (char *) boolector_get_opt_lng (tmpbtor, o);
    dflt = boolector_get_opt_dflt (tmpbtor, o);
    BTOR_NEW (res->mm, opt);
    opt->kind = o;
    opt->name = btor_mem_strdup (res->mm, lng);
    opt->val  = dflt;
    btor_hashptr_table_add (res->btor_opts, lng)->data.as_ptr = opt;
  }
  res->line = 1;
  boolector_delete(tmpbtor);
  return res;
}

static void
btorunt_delete (BtorUNT *unt)
{
  uint32_t i;
  BtorUNTBtorOpt *o;
  BtorPtrHashTableIterator it;
  BtorMemMgr *mm;

  mm = unt->mm;

  for (i = 0; i < BTOR_COUNT_STACK (unt->cl_btor_opts); i++)
  {
    o = BTOR_PEEK_STACK (unt->cl_btor_opts, i);
    assert (o);
    btor_mem_freestr (mm, o->name);
    BTOR_DELETE (mm, o);
  }
  BTOR_RELEASE_STACK (unt->cl_btor_opts);

  btor_iter_hashptr_init (&it, unt->btor_opts);
  while (btor_iter_hashptr_has_next (&it))
  {
    o = btor_iter_hashptr_next_data (&it)->as_ptr;
    assert (o);
    btor_mem_freestr (mm, o->name);
    BTOR_DELETE (mm, o);
  }
  btor_hashptr_table_delete (unt->btor_opts);

  BTOR_DELETE (mm, unt);
  btor_mem_mgr_delete (mm);
}

/*------------------------------------------------------------------------*/

static BtorUNT *g_btorunt;

/*------------------------------------------------------------------------*/

static void
btorunt_error (const char *msg, ...)
{
  va_list list;
  fputs ("btoruntrace: ", stderr);
  va_start (list, msg);
  vfprintf (stderr, msg, list);
  va_end (list);
  fputc ('\n', stderr);
  fflush (stderr);
  exit (1);
}

static void
btorunt_parse_error (const char *msg, ...)
{
  va_list list;
  fprintf (stderr,
           "btoruntrace: parse error in '%s' line %d: ",
           g_btorunt->filename,
           g_btorunt->line);
  va_start (list, msg);
  vfprintf (stderr, msg, list);
  va_end (list);
  fputc ('\n', stderr);
  fflush (stderr);
  exit (1);
}

#define BTORUNT_LOG(fmt, args...) \
  do                              \
  {                               \
    if (g_btorunt->verbosity)     \
    {                             \
      printf ("[btorunt] ");      \
      printf (fmt, ##args);       \
      printf ("\n");              \
    }                             \
  } while (0)

/*------------------------------------------------------------------------*/

static bool
btorunt_has_cl_btor_opt (BtorUNT *unt, BtorOption opt)
{
  assert (unt);

  uint32_t i;
  BtorUNTBtorOpt *o;

  for (i = 0; i < BTOR_COUNT_STACK (unt->cl_btor_opts); i++)
  {
    o = BTOR_PEEK_STACK (unt->cl_btor_opts, i);
    if (o->kind == opt) return true;
  }
  return false;
}

static BtorUNTBtorOpt *
btorunt_get_btor_opt (BtorUNT *unt, const char *opt)
{
  assert (unt);
  assert (opt);
  BtorPtrHashBucket *b;
  b = btor_hashptr_table_get (unt->btor_opts, (void *) opt);
  if (!b) btorunt_error ("Invalid Boolector option %s", opt);
  return b->data.as_ptr;
}

static bool
is_num_str (const char *str)
{
  const char *p;
  int32_t ch;
  if (*(p = str) == '-') p++;
  if (!isdigit ((int32_t) *p++)) return false;
  while (isdigit (ch = *p)) p++;
  return ch == 0;
}

void
parse_check_last_arg (char *op)
{
  if (strtok (0, " "))
  {
    btorunt_parse_error ("too many arguments for '%s'", op);
  }
}

static bool
parse_bool_arg (char *op)
{
  const char *tok;
  if (!(tok = strtok (0, " "))
      || (strcmp (tok, "true") && strcmp (tok, "false")))
  {
    btorunt_parse_error ("expected Boolean argument for '%s'", op);
  }
  assert (tok);
  return !strcmp (tok, "true") ? true : false;
}

static int32_t
parse_int_arg (char *op)
{
  const char *tok;
  if (!(tok = strtok (0, " ")) || !is_num_str (tok))
  {
    btorunt_parse_error ("expected integer argument for '%s'", op);
  }
  assert (tok);
  return atoi (tok);
}

static int32_t
parse_uint_arg (char *op)
{
  const char *tok;
  if (!(tok = strtok (0, " ")) || !is_num_str (tok) || tok[0] == '-')
  {
    btorunt_parse_error ("expected unsigned integer argument for '%s'", op);
  }
  assert (tok);
  return atoi (tok);
}

static char *
parse_str_arg (char *op)
{
  char *tok;
  if (!(tok = strtok (0, " ")))
  {
    btorunt_parse_error ("expected string argument for '%s'", op);
  }
  return tok;
}

#define PARSE_ARGS0(op) parse_check_last_arg (op);

#define PARSE_ARGS1(op, type1)             \
  arg1_##type1 = parse_##type1##_arg (op); \
  parse_check_last_arg (op);

#define PARSE_ARGS2(op, type1, type2)      \
  arg1_##type1 = parse_##type1##_arg (op); \
  arg2_##type2 = parse_##type2##_arg (op); \
  parse_check_last_arg (op);

#define PARSE_ARGS3(op, type1, type2, type3) \
  arg1_##type1 = parse_##type1##_arg (op);   \
  arg2_##type2 = parse_##type2##_arg (op);   \
  arg3_##type3 = parse_##type3##_arg (op);   \
  parse_check_last_arg (op);

/*--------------------------------------------------------------------------*/

static void *
hmap_get (BtorPtrHashTable *hmap, char *key)
{
  assert (hmap);
  assert (key);

  BtorPtrHashBucket *bucket;

  bucket = btor_hashptr_table_get (hmap, key);
  if (!bucket) btorunt_error ("'%s' is not hashed", key);
  assert (bucket);
  return bucket->data.as_ptr;
}

static BoolectorSort
get_sort (BtorPtrHashTable *hmap, char *key)
{
  return (BoolectorSort) (size_t) hmap_get (hmap, key);
}

static void
hmap_add (BtorPtrHashTable *hmap, char *key, void *value)
{
  assert (hmap);
  assert (key);

  BtorPtrHashBucket *bucket;

  bucket = btor_hashptr_table_get (hmap, key);
  if (!bucket)
  {
    char *key_cp;
    BTOR_NEWN (hmap->mm, key_cp, (strlen (key) + 1));
    strcpy (key_cp, key);
    bucket = btor_hashptr_table_add (hmap, key_cp);
  }
  assert (bucket);
  bucket->data.as_ptr = value;
}

static void
hmap_clear (BtorPtrHashTable *hmap)
{
  assert (hmap);

  BtorPtrHashBucket *bucket;

  for (bucket = hmap->first; bucket; bucket = hmap->first)
  {
    char *key = (char *) bucket->key;
    btor_hashptr_table_remove (hmap, key, NULL, NULL);
    BTOR_DELETEN (hmap->mm, key, (strlen (key) + 1));
  }
}

/*------------------------------------------------------------------------*/

#define RET_NONE 0
#define RET_VOIDPTR 1
#define RET_INT 2
#define RET_UINT 3
#define RET_CHARPTR 4
#define RET_ARRASS 5
#define RET_BOOL 6
#define RET_SKIP -1

BTOR_DECLARE_STACK (BoolectorSort, BoolectorSort);

#define BTOR_STR_LEN 40

void
parse (FILE *file)
{
  size_t i;
  int32_t ch;
  bool delete;
  uint32_t j, len, buffer_len, val;
  char *buffer, *tok, *basename;
  BoolectorNode **tmp;
  BtorPtrHashTable *hmap;
  BtorOption opt;
  Btor *btor;

  int32_t exp_ret;               /* expected return value */
  bool ret_bool;                 /* actual return value bool */
  int32_t ret_int;               /* actual return value int */
  uint32_t ret_uint;             /* actual return value unsigned int */
  char *ret_str;                 /* actual return value string */
  void *ret_ptr;                 /* actual return value string */
  char **res1_pptr, **res2_pptr; /* result pointer */

  char *btor_str; /* btor pointer string */
  char *exp_str;  /* expression string (pointer) */
  int32_t arg1_int, arg2_int, arg3_int;
  uint32_t arg3_uint;
  char *arg1_str, *arg2_str, *arg3_str;
  BtorIntStack arg_int;
  BtorCharPtrStack arg_str;
  BoolectorSortStack sort_stack;

  Btor *tmpbtor;
  FILE *outfile;
  int32_t flen, pres, pstat;
  char *outfilename, *emsg;

  BTORUNT_LOG ("parsing %s", g_btorunt->filename);

  delete = true;

  exp_ret    = RET_NONE;
  ret_int    = 0;
  ret_uint   = 0;
  ret_ptr    = 0;
  ret_str    = 0;
  ret_bool   = false;
  len        = 0;
  buffer_len = 256;
  arg2_int   = 0;
  btor       = 0;

  hmap = btor_hashptr_table_new (
      g_btorunt->mm, (BtorHashPtr) btor_hash_str, (BtorCmpPtr) strcmp);

  BTOR_CNEWN (g_btorunt->mm, buffer, buffer_len);

  BTOR_INIT_STACK (g_btorunt->mm, arg_int);
  BTOR_INIT_STACK (g_btorunt->mm, arg_str);
  BTOR_INIT_STACK (g_btorunt->mm, sort_stack);

  BTOR_CNEWN (g_btorunt->mm, btor_str, BTOR_STR_LEN);

NEXT:
  BTOR_RESET_STACK (arg_int);
  BTOR_RESET_STACK (arg_str);
  BTOR_RESET_STACK (sort_stack);
  ch = getc (file);
  if (ch == EOF) goto DONE;
  if (ch == '\r') goto NEXT;
  if (ch != '\n')
  {
    if (len + 1 >= buffer_len)
    {
      BTOR_REALLOC (g_btorunt->mm, buffer, buffer_len, buffer_len * 2);
      buffer_len *= 2;
      BTORUNT_LOG ("buffer resized");
    }
    buffer[len++] = ch;
    buffer[len]   = 0;
    goto NEXT;
  }
  BTORUNT_LOG ("  %d: %s", g_btorunt->line, buffer);

  /* NOTE take care of c function parameter evaluation order with more
   * than 1 argument */
  if (!(tok = strtok (buffer, " ")))
    btorunt_parse_error ("empty line");
  else if (exp_ret)
  {
    if (!strcmp (tok, "return"))
    {
      if (exp_ret == RET_VOIDPTR)
      {
        exp_str = parse_str_arg ("return");
        parse_check_last_arg ("return");
        hmap_add (hmap, exp_str, ret_ptr);
      }
      else if (exp_ret == RET_BOOL)
      {
        bool exp_bool = parse_bool_arg ("return");
        if (exp_bool != ret_bool)
          btorunt_error ("expected return value %s but got %s",
                         exp_bool ? "true" : "false",
                         ret_bool ? "true" : "false");
      }
      else if (exp_ret == RET_INT)
      {
        int32_t exp_int = parse_int_arg ("return");
        parse_check_last_arg ("return");
        if (exp_int != ret_int)
          btorunt_error (
              "expected return value %d but got %d", exp_int, ret_int);
      }
      else if (exp_ret == RET_UINT)
      {
        uint32_t exp_uint = parse_uint_arg ("return");
        parse_check_last_arg ("return");
        if (exp_uint != ret_uint)
          btorunt_error (
              "expected return value %d but got %d", exp_uint, ret_uint);
      }
      else if (exp_ret == RET_CHARPTR)
      {
        exp_str = parse_str_arg ("return");
        parse_check_last_arg ("return");
        if (strcmp (exp_str, ret_str))
          btorunt_error (
              "expected return string %s but got %s", exp_str, ret_str);
      }
      else if (exp_ret == RET_ARRASS)
      {
        PARSE_ARGS3 (tok, str, str, int);
        if (ret_int)
        {
          hmap_add (hmap, arg1_str, res1_pptr);
          hmap_add (hmap, arg2_str, res2_pptr);
        }
        if (arg3_int != ret_int)
          btorunt_error (
              "expected return value %d but got %d", arg3_int, ret_int);
      }
      else
        assert (exp_ret == RET_SKIP);
    }
    else
    {
      btorunt_parse_error ("return expected");
    }
    exp_ret = RET_NONE;
  }
  else
  {
    /* get btor object for all functions except for 'new' and 'get_btor' */
    if (strcmp (tok, "new") && strcmp (tok, "get_btor"))
    {
      exp_str = parse_str_arg (tok);
      len     = strlen (exp_str);
      for (j = 0; j < len; j++) btor_str[j] = exp_str[j];
      btor_str[j] = 0;
      btor        = hmap_get (hmap, btor_str);
      assert (btor);
    }
    if (!strcmp (tok, "chkclone"))
    {
      PARSE_ARGS0 (tok);
      boolector_chkclone (btor);
    }
    else if (!strcmp (tok, "new"))
    {
      PARSE_ARGS0 (tok);
      btor = boolector_new ();
      /* set btor options given via CL
       * (Note: overrules opt values set via trace file!) */
      for (i = 0; i < BTOR_COUNT_STACK (g_btorunt->cl_btor_opts); i++)
      {
        boolector_set_opt (btor,
                           BTOR_PEEK_STACK (g_btorunt->cl_btor_opts, i)->kind,
                           BTOR_PEEK_STACK (g_btorunt->cl_btor_opts, i)->val);
        BTORUNT_LOG (" *** set boolector option '%s' to '%u' (via CL)",
                     BTOR_PEEK_STACK (g_btorunt->cl_btor_opts, i)->name,
                     BTOR_PEEK_STACK (g_btorunt->cl_btor_opts, i)->val);
      }
      exp_ret = RET_VOIDPTR;
      ret_ptr = btor;
    }
    else if (!strcmp (tok, "clone"))
    {
      exp_ret = RET_VOIDPTR;
      ret_ptr = boolector_clone (btor);
    }
    else if (!strcmp (tok, "match_node_by_id"))
    {
      PARSE_ARGS1 (tok, int);
      ret_ptr = boolector_match_node_by_id (btor, arg1_int);
      exp_ret = RET_VOIDPTR;
    }
    else if (!strcmp (tok, "match_node_by_symbol"))
    {
      PARSE_ARGS1 (tok, str);
      ret_ptr = boolector_match_node_by_symbol (btor, arg1_str);
      exp_ret = RET_VOIDPTR;
    }
    else if (!strcmp (tok, "match_node"))
    {
      PARSE_ARGS1 (tok, str);
      ret_ptr = boolector_match_node (btor, hmap_get (hmap, arg1_str));
      exp_ret = RET_VOIDPTR;
    }
    else if (!strcmp (tok, "delete"))
    {
      PARSE_ARGS0 (tok);
      boolector_delete (btor);
      delete = false;
    }
    else if (!strcmp (tok, "set_btor_id"))
    {
      PARSE_ARGS2 (tok, str, int);
      boolector_set_btor_id (btor, hmap_get (hmap, arg1_str), arg2_int);
    }
    else if (!strcmp (tok, "get_btor_msg"))
    {
      PARSE_ARGS0 (tok);
      boolector_get_btor_msg (btor);
    }
    else if (!strcmp (tok, "set_msg_prefix"))
    {
      PARSE_ARGS1 (tok, str);
      boolector_set_msg_prefix (btor, arg1_str);
    }
    else if (!strcmp (tok, "reset_time"))
    {
      PARSE_ARGS0 (tok);
      boolector_reset_time (btor);
    }
    else if (!strcmp (tok, "reset_stats"))
    {
      PARSE_ARGS0 (tok);
      boolector_reset_stats (btor);
    }
    else if (!strcmp (tok, "print_stats"))
    {
      PARSE_ARGS0 (tok);
      boolector_print_stats (btor);
    }
    else if (!strcmp (tok, "assert"))
    {
      PARSE_ARGS1 (tok, str);
      boolector_assert (btor, hmap_get (hmap, arg1_str));
    }
    else if (!strcmp (tok, "assume"))
    {
      PARSE_ARGS1 (tok, str);
      boolector_assume (btor, hmap_get (hmap, arg1_str));
    }
    else if (!strcmp (tok, "reset_assumptions"))
    {
      PARSE_ARGS0 (tok);
      boolector_reset_assumptions (btor);
    }
    else if (!strcmp (tok, "fixate_assumptions"))
    {
      PARSE_ARGS0 (tok);
      boolector_fixate_assumptions (btor);
    }
    else if (!strcmp (tok, "failed"))
    {
      PARSE_ARGS1 (tok, str);
      ret_bool = boolector_failed (btor, hmap_get (hmap, arg1_str));
      exp_ret  = RET_BOOL;
    }
    else if (!strcmp (tok, "sat"))
    {
      PARSE_ARGS0 (tok);
      ret_int = boolector_sat (btor);
      exp_ret = g_btorunt->ignore_sat ? RET_SKIP : RET_INT;
    }
    else if (!strcmp (tok, "limited_sat"))
    {
      PARSE_ARGS2 (tok, int, int);
      ret_int = boolector_limited_sat (btor, arg1_int, arg2_int);
      exp_ret = g_btorunt->ignore_sat ? RET_SKIP : RET_INT;
    }
    else if (!strcmp (tok, "simplify"))
    {
      PARSE_ARGS0 (tok);
      ret_int = boolector_simplify (btor);
      exp_ret = RET_INT;
    }
    else if (!strcmp (tok, "set_sat_solver"))
    {
      PARSE_ARGS1 (tok, str);
      boolector_set_sat_solver (btor, arg1_str);
    }
    else if (!strcmp (tok, "set_opt"))
    {
      PARSE_ARGS2 (tok, str, int);
      opt = btorunt_get_btor_opt (g_btorunt, arg1_str)->kind;
      val = arg2_int;
      if (!btorunt_has_cl_btor_opt (g_btorunt, opt))
      {
        boolector_set_opt (btor, opt, val);
        BTORUNT_LOG ("     set boolector option '%s' to '%u' (via trace)",
                     arg1_str,
                     val);
      }
    }
    else if (!strcmp (tok, "get_opt"))
    {
      if (!g_btorunt->skip)
      {
        PARSE_ARGS1 (tok, str);
        opt     = btorunt_get_btor_opt (g_btorunt, arg1_str)->kind;
        ret_int = boolector_get_opt (btor, opt);
        exp_ret = RET_INT;
      }
      else
        exp_ret = RET_SKIP;
    }
    else if (!strcmp (tok, "get_opt_min"))
    {
      if (!g_btorunt->skip)
      {
        PARSE_ARGS1 (tok, str);
        opt     = btorunt_get_btor_opt (g_btorunt, arg1_str)->kind;
        ret_int = boolector_get_opt_min (btor, opt);
        exp_ret = RET_INT;
      }
      else
        exp_ret = RET_SKIP;
    }
    else if (!strcmp (tok, "get_opt_max"))
    {
      if (!g_btorunt->skip)
      {
        PARSE_ARGS1 (tok, str);
        opt     = btorunt_get_btor_opt (g_btorunt, arg1_str)->kind;
        ret_int = boolector_get_opt_max (btor, opt);
        exp_ret = RET_INT;
      }
      else
        exp_ret = RET_SKIP;
    }
    else if (!strcmp (tok, "get_opt_dflt"))
    {
      if (!g_btorunt->skip)
      {
        PARSE_ARGS1 (tok, str);
        opt     = btorunt_get_btor_opt (g_btorunt, arg1_str)->kind;
        ret_int = boolector_get_opt_dflt (btor, opt);
        exp_ret = RET_INT;
      }
      else
        exp_ret = RET_SKIP;
    }
    else if (!strcmp (tok, "get_opt_shrt"))
    {
      if (!g_btorunt->skip)
      {
        PARSE_ARGS1 (tok, str);
        opt     = btorunt_get_btor_opt (g_btorunt, arg1_str)->kind;
        ret_str = (void *) boolector_get_opt_shrt (btor, opt);
        exp_ret = RET_CHARPTR;
      }
      else
        exp_ret = RET_SKIP;
    }
    else if (!strcmp (tok, "get_opt_lng"))
    {
      if (!g_btorunt->skip)
      {
        PARSE_ARGS1 (tok, str);
        opt     = btorunt_get_btor_opt (g_btorunt, arg1_str)->kind;
        ret_str = (void *) boolector_get_opt_lng (btor, opt);
        exp_ret = RET_CHARPTR;
      }
      else
        exp_ret = RET_SKIP;
    }
    else if (!strcmp (tok, "get_opt_desc"))
    {
      if (!g_btorunt->skip)
      {
        PARSE_ARGS1 (tok, str);
        opt     = btorunt_get_btor_opt (g_btorunt, arg1_str)->kind;
        ret_str = (void *) boolector_get_opt_desc (btor, opt);
        exp_ret = RET_CHARPTR;
      }
      else
        exp_ret = RET_SKIP;
    }
    else if (!strcmp (tok, "has_opt"))
    {
      if (!g_btorunt->skip)
      {
        PARSE_ARGS1 (tok, str);
        opt     = btorunt_get_btor_opt (g_btorunt, arg1_str)->kind;
        ret_bool = boolector_has_opt (btor, opt);
        exp_ret = RET_BOOL;
      }
      else
        exp_ret = RET_SKIP;
    }
    else if (!strcmp (tok, "first_opt"))
    {
      if (!g_btorunt->skip)
      {
        PARSE_ARGS0 (tok);
        ret_int = boolector_first_opt (btor);
        exp_ret = RET_INT;
      }
      else
        exp_ret = RET_SKIP;
    }
    else if (!strcmp (tok, "next_opt"))
    {
      if (!g_btorunt->skip)
      {
        PARSE_ARGS1 (tok, str);
        opt     = btorunt_get_btor_opt (g_btorunt, arg1_str)->kind;
        ret_int = boolector_next_opt (btor, opt);
        exp_ret = RET_INT;
      }
      else
        exp_ret = RET_SKIP;
    }
    else if (!strcmp (tok, "copy"))
    {
      PARSE_ARGS1 (tok, str);
      ret_ptr = boolector_copy (btor, hmap_get (hmap, arg1_str));
      exp_ret = RET_VOIDPTR;
    }
    else if (!strcmp (tok, "release"))
    {
      PARSE_ARGS1 (tok, str);
      boolector_release (btor, hmap_get (hmap, arg1_str));
    }
    else if (!strcmp (tok, "release_all"))
    {
      PARSE_ARGS0 (tok);
      boolector_release_all (btor);
    }
    /* expressions */
    else if (!strcmp (tok, "const"))
    {
      PARSE_ARGS1 (tok, str);
      ret_ptr = boolector_const (btor, arg1_str);
      exp_ret = RET_VOIDPTR;
    }
    else if (!strcmp (tok, "constd"))
    {
      PARSE_ARGS2 (tok, str, str);
      ret_ptr = boolector_constd (btor, get_sort (hmap, arg1_str), arg2_str);
      exp_ret = RET_VOIDPTR;
    }
    else if (!strcmp (tok, "zero"))
    {
      PARSE_ARGS1 (tok, str);
      ret_ptr = boolector_zero (btor, get_sort (hmap, arg1_str));
      exp_ret = RET_VOIDPTR;
    }
    else if (!strcmp (tok, "false"))
    {
      PARSE_ARGS0 (tok);
      ret_ptr = boolector_false (btor);
      exp_ret = RET_VOIDPTR;
    }
    else if (!strcmp (tok, "ones"))
    {
      PARSE_ARGS1 (tok, str);
      ret_ptr = boolector_ones (btor, get_sort (hmap, arg1_str));
      exp_ret = RET_VOIDPTR;
    }
    else if (!strcmp (tok, "true"))
    {
      PARSE_ARGS0 (tok);
      ret_ptr = boolector_true (btor);
      exp_ret = RET_VOIDPTR;
    }
    else if (!strcmp (tok, "one"))
    {
      PARSE_ARGS1 (tok, str);
      ret_ptr = boolector_one (btor, get_sort (hmap, arg1_str));
      exp_ret = RET_VOIDPTR;
    }
    else if (!strcmp (tok, "min_signed"))
    {
      PARSE_ARGS1 (tok, str);
      ret_ptr = boolector_min_signed (btor, get_sort (hmap, arg1_str));
      exp_ret = RET_VOIDPTR;
    }
    else if (!strcmp (tok, "max_signed"))
    {
      PARSE_ARGS1 (tok, str);
      ret_ptr = boolector_max_signed (btor, get_sort (hmap, arg1_str));
      exp_ret = RET_VOIDPTR;
    }
    else if (!strcmp (tok, "unsigned_int"))
    {
      PARSE_ARGS2 (tok, int, str);
      ret_ptr =
          boolector_unsigned_int (btor, arg1_int, get_sort (hmap, arg2_str));
      exp_ret = RET_VOIDPTR;
    }
    else if (!strcmp (tok, "int"))
    {
      PARSE_ARGS2 (tok, int, str);
      ret_ptr = boolector_int (btor, arg1_int, get_sort (hmap, arg2_str));
      exp_ret = RET_VOIDPTR;
    }
    else if (!strcmp (tok, "var"))
    {
      PARSE_ARGS2 (tok, str, str);
      arg2_str = !strcmp (arg2_str, "(null)") ? 0 : arg2_str;
      ret_ptr  = boolector_var (btor, get_sort (hmap, arg1_str), arg2_str);
      exp_ret  = RET_VOIDPTR;
    }
    else if (!strcmp (tok, "array"))
    {
      PARSE_ARGS2 (tok, str, str);
      arg2_str = !strcmp (arg2_str, "(null)") ? 0 : arg2_str;
      ret_ptr  = boolector_array (btor, get_sort (hmap, arg1_str), arg2_str);
      exp_ret  = RET_VOIDPTR;
    }
    else if (!strcmp (tok, "uf"))
    {
      PARSE_ARGS2 (tok, str, str);
      arg2_str = !strcmp (arg2_str, "(null)") ? 0 : arg2_str;
      ret_ptr  = boolector_uf (btor, get_sort (hmap, arg1_str), arg2_str);
      exp_ret  = RET_VOIDPTR;
    }
    else if (!strcmp (tok, "not"))
    {
      PARSE_ARGS1 (tok, str);
      ret_ptr = boolector_not (btor, hmap_get (hmap, arg1_str));
      exp_ret = RET_VOIDPTR;
    }
    else if (!strcmp (tok, "neg"))
    {
      PARSE_ARGS1 (tok, str);
      ret_ptr = boolector_neg (btor, hmap_get (hmap, arg1_str));
      exp_ret = RET_VOIDPTR;
    }
    else if (!strcmp (tok, "redor"))
    {
      PARSE_ARGS1 (tok, str);
      ret_ptr = boolector_redor (btor, hmap_get (hmap, arg1_str));
      exp_ret = RET_VOIDPTR;
    }
    else if (!strcmp (tok, "redxor"))
    {
      PARSE_ARGS1 (tok, str);
      ret_ptr = boolector_redxor (btor, hmap_get (hmap, arg1_str));
      exp_ret = RET_VOIDPTR;
    }
    else if (!strcmp (tok, "redand"))
    {
      PARSE_ARGS1 (tok, str);
      ret_ptr = boolector_redand (btor, hmap_get (hmap, arg1_str));
      exp_ret = RET_VOIDPTR;
    }
    else if (!strcmp (tok, "slice"))
    {
      PARSE_ARGS3 (tok, str, int, int);
      ret_ptr =
          boolector_slice (btor, hmap_get (hmap, arg1_str), arg2_int, arg3_int);
      exp_ret = RET_VOIDPTR;
    }
    else if (!strcmp (tok, "uext"))
    {
      PARSE_ARGS2 (tok, str, int);
      ret_ptr = boolector_uext (btor, hmap_get (hmap, arg1_str), arg2_int);
      exp_ret = RET_VOIDPTR;
    }
    else if (!strcmp (tok, "sext"))
    {
      PARSE_ARGS2 (tok, str, int);
      ret_ptr = boolector_sext (btor, hmap_get (hmap, arg1_str), arg2_int);
      exp_ret = RET_VOIDPTR;
    }
    else if (!strcmp (tok, "implies"))
    {
      PARSE_ARGS2 (tok, str, str);
      ret_ptr = boolector_implies (
          btor, hmap_get (hmap, arg1_str), hmap_get (hmap, arg2_str));
      exp_ret = RET_VOIDPTR;
    }
    else if (!strcmp (tok, "iff"))
    {
      PARSE_ARGS2 (tok, str, str);
      ret_ptr = boolector_iff (
          btor, hmap_get (hmap, arg1_str), hmap_get (hmap, arg2_str));
      exp_ret = RET_VOIDPTR;
    }
    else if (!strcmp (tok, "xor"))
    {
      PARSE_ARGS2 (tok, str, str);
      ret_ptr = boolector_xor (
          btor, hmap_get (hmap, arg1_str), hmap_get (hmap, arg2_str));
      exp_ret = RET_VOIDPTR;
    }
    else if (!strcmp (tok, "xnor"))
    {
      PARSE_ARGS2 (tok, str, str);
      ret_ptr = boolector_xnor (
          btor, hmap_get (hmap, arg1_str), hmap_get (hmap, arg2_str));
      exp_ret = RET_VOIDPTR;
    }
    else if (!strcmp (tok, "and"))
    {
      PARSE_ARGS2 (tok, str, str);
      ret_ptr = boolector_and (
          btor, hmap_get (hmap, arg1_str), hmap_get (hmap, arg2_str));
      exp_ret = RET_VOIDPTR;
    }
    else if (!strcmp (tok, "nand"))
    {
      PARSE_ARGS2 (tok, str, str);
      ret_ptr = boolector_nand (
          btor, hmap_get (hmap, arg1_str), hmap_get (hmap, arg2_str));
      exp_ret = RET_VOIDPTR;
    }
    else if (!strcmp (tok, "or"))
    {
      PARSE_ARGS2 (tok, str, str);
      ret_ptr = boolector_or (
          btor, hmap_get (hmap, arg1_str), hmap_get (hmap, arg2_str));
      exp_ret = RET_VOIDPTR;
    }
    else if (!strcmp (tok, "nor"))
    {
      PARSE_ARGS2 (tok, str, str);
      ret_ptr = boolector_nor (
          btor, hmap_get (hmap, arg1_str), hmap_get (hmap, arg2_str));
      exp_ret = RET_VOIDPTR;
    }
    else if (!strcmp (tok, "eq"))
    {
      PARSE_ARGS2 (tok, str, str);
      ret_ptr = boolector_eq (
          btor, hmap_get (hmap, arg1_str), hmap_get (hmap, arg2_str));
      exp_ret = RET_VOIDPTR;
    }
    else if (!strcmp (tok, "ne"))
    {
      PARSE_ARGS2 (tok, str, str);
      ret_ptr = boolector_ne (
          btor, hmap_get (hmap, arg1_str), hmap_get (hmap, arg2_str));
      exp_ret = RET_VOIDPTR;
    }
    else if (!strcmp (tok, "add"))
    {
      PARSE_ARGS2 (tok, str, str);
      ret_ptr = boolector_add (
          btor, hmap_get (hmap, arg1_str), hmap_get (hmap, arg2_str));
      exp_ret = RET_VOIDPTR;
    }
    else if (!strcmp (tok, "uaddo"))
    {
      PARSE_ARGS2 (tok, str, str);
      ret_ptr = boolector_uaddo (
          btor, hmap_get (hmap, arg1_str), hmap_get (hmap, arg2_str));
      exp_ret = RET_VOIDPTR;
    }
    else if (!strcmp (tok, "saddo"))
    {
      PARSE_ARGS2 (tok, str, str);
      ret_ptr = boolector_saddo (
          btor, hmap_get (hmap, arg1_str), hmap_get (hmap, arg2_str));
      exp_ret = RET_VOIDPTR;
    }
    else if (!strcmp (tok, "mul"))
    {
      PARSE_ARGS2 (tok, str, str);
      ret_ptr = boolector_mul (
          btor, hmap_get (hmap, arg1_str), hmap_get (hmap, arg2_str));
      exp_ret = RET_VOIDPTR;
    }
    else if (!strcmp (tok, "umulo"))
    {
      PARSE_ARGS2 (tok, str, str);
      ret_ptr = boolector_umulo (
          btor, hmap_get (hmap, arg1_str), hmap_get (hmap, arg2_str));
      exp_ret = RET_VOIDPTR;
    }
    else if (!strcmp (tok, "smulo"))
    {
      PARSE_ARGS2 (tok, str, str);
      ret_ptr = boolector_smulo (
          btor, hmap_get (hmap, arg1_str), hmap_get (hmap, arg2_str));
      exp_ret = RET_VOIDPTR;
    }
    else if (!strcmp (tok, "ult"))
    {
      PARSE_ARGS2 (tok, str, str);
      ret_ptr = boolector_ult (
          btor, hmap_get (hmap, arg1_str), hmap_get (hmap, arg2_str));
      exp_ret = RET_VOIDPTR;
    }
    else if (!strcmp (tok, "slt"))
    {
      PARSE_ARGS2 (tok, str, str);
      ret_ptr = boolector_slt (
          btor, hmap_get (hmap, arg1_str), hmap_get (hmap, arg2_str));
      exp_ret = RET_VOIDPTR;
    }
    else if (!strcmp (tok, "ulte"))
    {
      PARSE_ARGS2 (tok, str, str);
      ret_ptr = boolector_ulte (
          btor, hmap_get (hmap, arg1_str), hmap_get (hmap, arg2_str));
      exp_ret = RET_VOIDPTR;
    }
    else if (!strcmp (tok, "slte"))
    {
      PARSE_ARGS2 (tok, str, str);
      ret_ptr = boolector_slte (
          btor, hmap_get (hmap, arg1_str), hmap_get (hmap, arg2_str));
      exp_ret = RET_VOIDPTR;
    }
    else if (!strcmp (tok, "ugt"))
    {
      PARSE_ARGS2 (tok, str, str);
      ret_ptr = boolector_ugt (
          btor, hmap_get (hmap, arg1_str), hmap_get (hmap, arg2_str));
      exp_ret = RET_VOIDPTR;
    }
    else if (!strcmp (tok, "sgt"))
    {
      PARSE_ARGS2 (tok, str, str);
      ret_ptr = boolector_sgt (
          btor, hmap_get (hmap, arg1_str), hmap_get (hmap, arg2_str));
      exp_ret = RET_VOIDPTR;
    }
    else if (!strcmp (tok, "ugte"))
    {
      PARSE_ARGS2 (tok, str, str);
      ret_ptr = boolector_ugte (
          btor, hmap_get (hmap, arg1_str), hmap_get (hmap, arg2_str));
      exp_ret = RET_VOIDPTR;
    }
    else if (!strcmp (tok, "sgte"))
    {
      PARSE_ARGS2 (tok, str, str);
      ret_ptr = boolector_sgte (
          btor, hmap_get (hmap, arg1_str), hmap_get (hmap, arg2_str));
      exp_ret = RET_VOIDPTR;
    }
    else if (!strcmp (tok, "sll"))
    {
      PARSE_ARGS2 (tok, str, str);
      ret_ptr = boolector_sll (
          btor, hmap_get (hmap, arg1_str), hmap_get (hmap, arg2_str));
      exp_ret = RET_VOIDPTR;
    }
    else if (!strcmp (tok, "srl"))
    {
      PARSE_ARGS2 (tok, str, str);
      ret_ptr = boolector_srl (
          btor, hmap_get (hmap, arg1_str), hmap_get (hmap, arg2_str));
      exp_ret = RET_VOIDPTR;
    }
    else if (!strcmp (tok, "sra"))
    {
      PARSE_ARGS2 (tok, str, str);
      ret_ptr = boolector_sra (
          btor, hmap_get (hmap, arg1_str), hmap_get (hmap, arg2_str));
      exp_ret = RET_VOIDPTR;
    }
    else if (!strcmp (tok, "rol"))
    {
      PARSE_ARGS2 (tok, str, str);
      ret_ptr = boolector_rol (
          btor, hmap_get (hmap, arg1_str), hmap_get (hmap, arg2_str));
      exp_ret = RET_VOIDPTR;
    }
    else if (!strcmp (tok, "ror"))
    {
      PARSE_ARGS2 (tok, str, str);
      ret_ptr = boolector_ror (
          btor, hmap_get (hmap, arg1_str), hmap_get (hmap, arg2_str));
      exp_ret = RET_VOIDPTR;
    }
    else if (!strcmp (tok, "sub"))
    {
      PARSE_ARGS2 (tok, str, str);
      ret_ptr = boolector_sub (
          btor, hmap_get (hmap, arg1_str), hmap_get (hmap, arg2_str));
      exp_ret = RET_VOIDPTR;
    }
    else if (!strcmp (tok, "usubo"))
    {
      PARSE_ARGS2 (tok, str, str);
      ret_ptr = boolector_usubo (
          btor, hmap_get (hmap, arg1_str), hmap_get (hmap, arg2_str));
      exp_ret = RET_VOIDPTR;
    }
    else if (!strcmp (tok, "ssubo"))
    {
      PARSE_ARGS2 (tok, str, str);
      ret_ptr = boolector_ssubo (
          btor, hmap_get (hmap, arg1_str), hmap_get (hmap, arg2_str));
      exp_ret = RET_VOIDPTR;
    }
    else if (!strcmp (tok, "udiv"))
    {
      PARSE_ARGS2 (tok, str, str);
      ret_ptr = boolector_udiv (
          btor, hmap_get (hmap, arg1_str), hmap_get (hmap, arg2_str));
      exp_ret = RET_VOIDPTR;
    }
    else if (!strcmp (tok, "sdiv"))
    {
      PARSE_ARGS2 (tok, str, str);
      ret_ptr = boolector_sdiv (
          btor, hmap_get (hmap, arg1_str), hmap_get (hmap, arg2_str));
      exp_ret = RET_VOIDPTR;
    }
    else if (!strcmp (tok, "sdivo"))
    {
      PARSE_ARGS2 (tok, str, str);
      ret_ptr = boolector_sdivo (
          btor, hmap_get (hmap, arg1_str), hmap_get (hmap, arg2_str));
      exp_ret = RET_VOIDPTR;
    }
    else if (!strcmp (tok, "urem"))
    {
      PARSE_ARGS2 (tok, str, str);
      ret_ptr = boolector_urem (
          btor, hmap_get (hmap, arg1_str), hmap_get (hmap, arg2_str));
      exp_ret = RET_VOIDPTR;
    }
    else if (!strcmp (tok, "srem"))
    {
      PARSE_ARGS2 (tok, str, str);
      ret_ptr = boolector_srem (
          btor, hmap_get (hmap, arg1_str), hmap_get (hmap, arg2_str));
      exp_ret = RET_VOIDPTR;
    }
    else if (!strcmp (tok, "smod"))
    {
      PARSE_ARGS2 (tok, str, str);
      ret_ptr = boolector_smod (
          btor, hmap_get (hmap, arg1_str), hmap_get (hmap, arg2_str));
      exp_ret = RET_VOIDPTR;
    }
    else if (!strcmp (tok, "concat"))
    {
      PARSE_ARGS2 (tok, str, str);
      ret_ptr = boolector_concat (
          btor, hmap_get (hmap, arg1_str), hmap_get (hmap, arg2_str));
      exp_ret = RET_VOIDPTR;
    }
    else if (!strcmp (tok, "repeat"))
    {
      PARSE_ARGS2 (tok, str, int);
      ret_ptr = boolector_repeat (btor, hmap_get (hmap, arg1_str), arg2_int);
      exp_ret = RET_VOIDPTR;
    }
    else if (!strcmp (tok, "read"))
    {
      PARSE_ARGS2 (tok, str, str);
      ret_ptr = boolector_read (
          btor, hmap_get (hmap, arg1_str), hmap_get (hmap, arg2_str));
      exp_ret = RET_VOIDPTR;
    }
    else if (!strcmp (tok, "write"))
    {
      PARSE_ARGS3 (tok, str, str, str);
      ret_ptr = boolector_write (btor,
                                 hmap_get (hmap, arg1_str),
                                 hmap_get (hmap, arg2_str),
                                 hmap_get (hmap, arg3_str));
      exp_ret = RET_VOIDPTR;
    }
    else if (!strcmp (tok, "cond"))
    {
      PARSE_ARGS3 (tok, str, str, str);
      ret_ptr = boolector_cond (btor,
                                hmap_get (hmap, arg1_str),
                                hmap_get (hmap, arg2_str),
                                hmap_get (hmap, arg3_str));
      exp_ret = RET_VOIDPTR;
    }
    else if (!strcmp (tok, "param"))
    {
      PARSE_ARGS2 (tok, str, str);
      arg2_str = !strcmp (arg2_str, "(null)") ? 0 : arg2_str;
      ret_ptr  = boolector_param (btor, get_sort (hmap, arg1_str), arg2_str);
      exp_ret  = RET_VOIDPTR;
    }
    else if (!strcmp (tok, "fun"))
    {
      uint32_t arg1_uint = parse_uint_arg (tok); /* paramc */
      BTOR_NEWN (g_btorunt->mm, tmp, arg1_uint); /* params */
      for (i = 0; i < arg1_uint; i++)
        tmp[i] = hmap_get (hmap, parse_str_arg (tok));
      arg1_str = parse_str_arg (tok); /* function body */
      parse_check_last_arg (tok);
      ret_ptr = boolector_fun (btor, tmp, arg1_uint, hmap_get (hmap, arg1_str));
      BTOR_DELETEN (g_btorunt->mm, tmp, arg1_uint);
      exp_ret = RET_VOIDPTR;
    }
    else if (!strcmp (tok, "exists"))
    {
      uint32_t arg1_uint = parse_uint_arg (tok);
      BTOR_NEWN (g_btorunt->mm, tmp, arg1_uint); /* vars */
      for (i = 0; i < arg1_uint; i++)
        tmp[i] = hmap_get (hmap, parse_str_arg (tok));
      arg1_str = parse_str_arg (tok); /* body */
      parse_check_last_arg (tok);
      ret_ptr =
          boolector_exists (btor, tmp, arg1_uint, hmap_get (hmap, arg1_str));
      BTOR_DELETEN (g_btorunt->mm, tmp, arg1_uint);
      exp_ret = RET_VOIDPTR;
    }
    else if (!strcmp (tok, "forall"))
    {
      uint32_t arg1_uint = parse_uint_arg (tok);
      BTOR_NEWN (g_btorunt->mm, tmp, arg1_uint); /* vars */
      for (i = 0; i < arg1_uint; i++)
        tmp[i] = hmap_get (hmap, parse_str_arg (tok));
      arg1_str = parse_str_arg (tok); /* body */
      parse_check_last_arg (tok);
      ret_ptr =
          boolector_forall (btor, tmp, arg1_uint, hmap_get (hmap, arg1_str));
      BTOR_DELETEN (g_btorunt->mm, tmp, arg1_uint);
      exp_ret = RET_VOIDPTR;
    }
    else if (!strcmp (tok, "apply"))
    {
      uint32_t arg1_uint = parse_uint_arg (tok); /* argc */
      BTOR_NEWN (g_btorunt->mm, tmp, arg1_uint); /* args */
      for (i = 0; i < arg1_uint; i++)
        tmp[i] = hmap_get (hmap, parse_str_arg (tok));
      arg1_str = parse_str_arg (tok); /* function */
      parse_check_last_arg (tok);
      ret_ptr =
          boolector_apply (btor, tmp, arg1_uint, hmap_get (hmap, arg1_str));
      BTOR_DELETEN (g_btorunt->mm, tmp, arg1_uint);
      exp_ret = RET_VOIDPTR;
    }
    else if (!strcmp (tok, "inc"))
    {
      PARSE_ARGS1 (tok, str);
      ret_ptr = boolector_inc (btor, hmap_get (hmap, arg1_str));
      exp_ret = RET_VOIDPTR;
    }
    else if (!strcmp (tok, "dec"))
    {
      PARSE_ARGS1 (tok, str);
      ret_ptr = boolector_dec (btor, hmap_get (hmap, arg1_str));
      exp_ret = RET_VOIDPTR;
    }
    /* getter */
    else if (!strcmp (tok, "get_refs"))
    {
      PARSE_ARGS0 (tok);
      if (!g_btorunt->skip)
      {
        ret_int = boolector_get_refs (btor);
        exp_ret = RET_INT;
      }
      else
        exp_ret = RET_SKIP;
    }
    else if (!strcmp (tok, "get_node_id"))
    {
      PARSE_ARGS1 (tok, str);
      if (!g_btorunt->skip)
      {
        ret_int = boolector_get_node_id (btor, hmap_get (hmap, arg1_str));
        exp_ret = RET_INT;
      }
      else
        exp_ret = RET_SKIP;
    }
    else if (!strcmp (tok, "get_symbol"))
    {
      PARSE_ARGS1 (tok, str);
      if (!g_btorunt->skip)
      {
        ret_str =
            (char *) boolector_get_symbol (btor, hmap_get (hmap, arg1_str));
        if (!ret_str) ret_str = "(null)";
        exp_ret = RET_CHARPTR;
      }
      else
        exp_ret = RET_SKIP;
    }
    else if (!strcmp (tok, "set_symbol"))
    {
      PARSE_ARGS2 (tok, str, str);
      boolector_set_symbol (btor, hmap_get (hmap, arg1_str), arg2_str);
    }
    else if (!strcmp (tok, "get_width"))
    {
      PARSE_ARGS1 (tok, str);
      if (!g_btorunt->skip)
      {
        ret_int = boolector_get_width (btor, hmap_get (hmap, arg1_str));
        exp_ret = RET_INT;
      }
      else
        exp_ret = RET_SKIP;
    }
    else if (!strcmp (tok, "get_index_width"))
    {
      PARSE_ARGS1 (tok, str);
      if (!g_btorunt->skip)
      {
        ret_int = boolector_get_index_width (btor, hmap_get (hmap, arg1_str));
        exp_ret = RET_INT;
      }
      else
        exp_ret = RET_SKIP;
    }
    else if (!strcmp (tok, "get_bits"))
    {
      PARSE_ARGS1 (tok, str);
      ret_ptr = (char *) boolector_get_bits (btor, hmap_get (hmap, arg1_str));
      exp_ret = RET_VOIDPTR;
    }
    else if (!strcmp (tok, "free_bits"))
    {
      PARSE_ARGS1 (tok, str);
      boolector_free_bits (btor, hmap_get (hmap, arg1_str));
    }
    else if (!strcmp (tok, "get_fun_arity"))
    {
      PARSE_ARGS1 (tok, str);
      if (!g_btorunt->skip)
      {
        ret_int = boolector_get_fun_arity (btor, hmap_get (hmap, arg1_str));
        exp_ret = RET_INT;
      }
      else
        exp_ret = RET_SKIP;
    }
    else if (!strcmp (tok, "get_btor"))
    {
      PARSE_ARGS1 (tok, str);
      if (!g_btorunt->skip)
      {
        ret_ptr = boolector_get_btor (hmap_get (hmap, arg1_str));
        exp_ret = RET_VOIDPTR;
      }
      else
        exp_ret = RET_SKIP;
    }
    else if (!strcmp (tok, "is_const"))
    {
      PARSE_ARGS1 (tok, str);
      if (!g_btorunt->skip)
      {
        ret_bool = boolector_is_const (btor, hmap_get (hmap, arg1_str));
        exp_ret  = RET_BOOL;
      }
      else
        exp_ret = RET_SKIP;
    }
    else if (!strcmp (tok, "is_var"))
    {
      PARSE_ARGS1 (tok, str);
      if (!g_btorunt->skip)
      {
        ret_bool = boolector_is_var (btor, hmap_get (hmap, arg1_str));
        exp_ret  = RET_BOOL;
      }
      else
        exp_ret = RET_SKIP;
    }
    else if (!strcmp (tok, "is_array"))
    {
      PARSE_ARGS1 (tok, str);
      if (!g_btorunt->skip)
      {
        ret_bool = boolector_is_array (btor, hmap_get (hmap, arg1_str));
        exp_ret  = RET_BOOL;
      }
      else
        exp_ret = RET_SKIP;
    }
    else if (!strcmp (tok, "is_array_var"))
    {
      PARSE_ARGS1 (tok, str);
      if (!g_btorunt->skip)
      {
        ret_bool = boolector_is_array_var (btor, hmap_get (hmap, arg1_str));
        exp_ret  = RET_BOOL;
      }
      else
        exp_ret = RET_SKIP;
    }
    else if (!strcmp (tok, "is_param"))
    {
      PARSE_ARGS1 (tok, str);
      if (!g_btorunt->skip)
      {
        ret_bool = boolector_is_param (btor, hmap_get (hmap, arg1_str));
        exp_ret  = RET_BOOL;
      }
      else
        exp_ret = RET_SKIP;
    }
    else if (!strcmp (tok, "is_bound_param"))
    {
      PARSE_ARGS1 (tok, str);
      if (!g_btorunt->skip)
      {
        ret_bool = boolector_is_bound_param (btor, hmap_get (hmap, arg1_str));
        exp_ret  = RET_BOOL;
      }
      else
        exp_ret = RET_SKIP;
    }
    else if (!strcmp (tok, "is_uf"))
    {
      PARSE_ARGS1 (tok, str);
      if (!g_btorunt->skip)
      {
        ret_bool = boolector_is_uf (btor, hmap_get (hmap, arg1_str));
        exp_ret  = RET_BOOL;
      }
      else
        exp_ret = RET_SKIP;
    }
    else if (!strcmp (tok, "is_fun"))
    {
      PARSE_ARGS1 (tok, str);
      if (!g_btorunt->skip)
      {
        ret_bool = boolector_is_fun (btor, hmap_get (hmap, arg1_str));
        exp_ret  = RET_BOOL;
      }
      else
        exp_ret = RET_SKIP;
    }
    else if (!strcmp (tok, "fun_sort_check"))
    {
      uint32_t arg1_uint = parse_uint_arg (tok); /* argc */
      BTOR_NEWN (g_btorunt->mm, tmp, arg1_uint);
      for (i = 0; i < arg1_uint; i++) /* args */
        tmp[i] = hmap_get (hmap, parse_str_arg (tok));
      arg1_str = parse_str_arg (tok); /* function body */
      parse_check_last_arg (tok);
      ret_int = boolector_fun_sort_check (
          btor, tmp, arg1_uint, hmap_get (hmap, arg1_str));
      exp_ret = RET_SKIP;
      BTOR_DELETEN (g_btorunt->mm, tmp, arg1_uint);
    }
    else if (!strcmp (tok, "bv_assignment"))
    {
      PARSE_ARGS1 (tok, str);
      ret_ptr =
          (char *) boolector_bv_assignment (btor, hmap_get (hmap, arg1_str));
      exp_ret = RET_VOIDPTR;
    }
    else if (!strcmp (tok, "free_bv_assignment"))
    {
      PARSE_ARGS1 (tok, str);
      boolector_free_bv_assignment (btor, hmap_get (hmap, arg1_str));
    }
    else if (!strcmp (tok, "array_assignment"))
    {
      PARSE_ARGS1 (tok, str);
      boolector_array_assignment (
          btor, hmap_get (hmap, arg1_str), &res1_pptr, &res2_pptr, &ret_uint);
      exp_ret = RET_ARRASS;
    }
    else if (!strcmp (tok, "free_array_assignment"))
    {
      PARSE_ARGS3 (tok, str, str, uint);
      boolector_free_array_assignment (btor,
                                       hmap_get (hmap, arg1_str),
                                       hmap_get (hmap, arg2_str),
                                       arg3_uint);
    }
    else if (!strcmp (tok, "uf_assignment"))
    {
      PARSE_ARGS1 (tok, str);
      boolector_uf_assignment (
          btor, hmap_get (hmap, arg1_str), &res1_pptr, &res2_pptr, &ret_uint);
      exp_ret = RET_ARRASS;
    }
    else if (!strcmp (tok, "free_uf_assignment"))
    {
      PARSE_ARGS3 (tok, str, str, uint);
      boolector_free_uf_assignment (btor,
                                    hmap_get (hmap, arg1_str),
                                    hmap_get (hmap, arg2_str),
                                    arg3_uint);
    }
    else if (!strcmp (tok, "print_model"))
    {
      PARSE_ARGS1 (tok, str);
      boolector_print_model (btor, arg1_str, stdout);
    }
    else if (!strcmp (tok, "print_value_smt2"))
    {
      PARSE_ARGS2 (tok, str, str);
      boolector_print_value_smt2 (
          btor, hmap_get (hmap, arg1_str), arg2_str, stdout);
    }
    /* sorts */
    else if (!strcmp (tok, "bool_sort"))
    {
      PARSE_ARGS0 (tok);
      ret_ptr = (void *) (size_t) boolector_bool_sort (btor);
      exp_ret = RET_VOIDPTR;
    }
    else if (!strcmp (tok, "bitvec_sort"))
    {
      PARSE_ARGS1 (tok, int);
      ret_ptr = (void *) (size_t) boolector_bitvec_sort (btor, arg1_int);
      exp_ret = RET_VOIDPTR;
    }
    else if (!strcmp (tok, "array_sort"))
    {
      PARSE_ARGS2 (tok, str, str);
      ret_ptr = (void *) (size_t) boolector_array_sort (
          btor, get_sort (hmap, arg1_str), get_sort (hmap, arg2_str));
      exp_ret = RET_VOIDPTR;
    }
    else if (!strcmp (tok, "copy_sort"))
    {
      PARSE_ARGS1 (tok, str);
      ret_ptr = (void *) (size_t) boolector_copy_sort (
          btor, get_sort (hmap, arg1_str));
      exp_ret = RET_VOIDPTR;
    }
    else if (!strcmp (tok, "fun_sort"))
    {
      while ((tok = strtok (0, " ")))
        BTOR_PUSH_STACK (sort_stack, get_sort (hmap, tok));
      assert (BTOR_COUNT_STACK (sort_stack) >= 2);
      ret_ptr = (void *) (size_t) boolector_fun_sort (
          btor,
          sort_stack.start,
          BTOR_COUNT_STACK (sort_stack) - 1,
          BTOR_TOP_STACK (sort_stack));
      exp_ret = RET_VOIDPTR;
    }
    else if (!strcmp (tok, "release_sort"))
    {
      PARSE_ARGS1 (tok, str);
      boolector_release_sort (btor, get_sort (hmap, arg1_str));
    }
    else if (!strcmp (tok, "is_equal_sort"))
    {
      PARSE_ARGS2 (tok, str, str);
      ret_bool = boolector_is_equal_sort (
          btor, hmap_get (hmap, arg1_str), hmap_get (hmap, arg2_str));
      exp_ret = RET_BOOL;
    }
    else if (!strcmp (tok, "is_array_sort"))
    {
      PARSE_ARGS1 (tok, str);
      ret_bool = boolector_is_array_sort (btor, get_sort (hmap, arg1_str));
      exp_ret  = RET_BOOL;
    }
    else if (!strcmp (tok, "is_fun_sort"))
    {
      PARSE_ARGS1 (tok, str);
      if (!g_btorunt->skip)
      {
        ret_bool = boolector_is_fun_sort (btor, get_sort (hmap, arg1_str));
        exp_ret  = RET_BOOL;
      }
      else
        exp_ret = RET_SKIP;
    }
    else if (!strcmp (tok, "is_bitvec_sort"))
    {
      PARSE_ARGS1 (tok, str);
      if (!g_btorunt->skip)
      {
        ret_bool = boolector_is_bitvec_sort (btor, get_sort (hmap, arg1_str));
        exp_ret  = RET_BOOL;
      }
      else
        exp_ret = RET_SKIP;
    }
    else if (!strcmp (tok, "get_sort"))
    {
      PARSE_ARGS1 (tok, str);
      ret_ptr = boolector_get_sort (btor, hmap_get (hmap, arg1_str));
      exp_ret = RET_VOIDPTR;
    }
    else if (!strcmp (tok, "fun_get_domain_sort"))
    {
      PARSE_ARGS1 (tok, str);
      ret_ptr = boolector_fun_get_domain_sort (btor, hmap_get (hmap, arg1_str));
      exp_ret = RET_VOIDPTR;
    }
    else if (!strcmp (tok, "fun_get_codomain_sort"))
    {
      PARSE_ARGS1 (tok, str);
      ret_ptr =
          boolector_fun_get_codomain_sort (btor, hmap_get (hmap, arg1_str));
      exp_ret = RET_VOIDPTR;
    }
    /* dumping */
    else if (!strcmp (tok, "dump_btor_node"))
    {
      PARSE_ARGS1 (tok, str);
      boolector_dump_btor_node (btor, stdout, hmap_get (hmap, arg1_str));
    }
    else if (!strcmp (tok, "dump_smt2_node"))
    {
      PARSE_ARGS1 (tok, str);
      boolector_dump_smt2_node (btor, stdout, hmap_get (hmap, arg1_str));
    }
    else if (!strcmp (tok, "dump_btor") || !strcmp (tok, "dump_smt2"))
    {
      PARSE_ARGS0 (tok);

      if (g_btorunt->dump_stdout)
      {
        if (!strcmp (tok, "dump_btor"))
          boolector_dump_btor (btor, stdout);
        else
          boolector_dump_smt2 (btor, stdout);
      }
      else
      {
        basename = strrchr (g_btorunt->filename, '/');
        if (basename)
          basename += 1; /* skip '/' character */
        else
          basename = g_btorunt->filename;
        flen = 40 + strlen ("/tmp/") + strlen (basename);
        BTOR_NEWN (g_btorunt->mm, outfilename, flen);

        if (!strcmp (tok, "dump_btor"))
        {
          sprintf (outfilename, "/tmp/%s.%s", basename, "btor");
          outfile = fopen (outfilename, "w");
          assert (outfile);
          boolector_dump_btor (btor, outfile);
        }
        else
        {
          sprintf (outfilename, "/tmp/%s.%s", basename, "smt2");
          outfile = fopen (outfilename, "w");
          assert (outfile);
          boolector_dump_smt2 (btor, outfile);
        }

        BTORUNT_LOG ("dump formula to %s", outfilename);
        fclose (outfile);
        outfile = fopen (outfilename, "r");
        tmpbtor = boolector_new ();
        boolector_set_opt (tmpbtor, BTOR_OPT_PARSE_INTERACTIVE, 0);
        pres = boolector_parse (
            tmpbtor, outfile, outfilename, stdout, &emsg, &pstat);
        (void) pres;
        if (emsg)
          fprintf (stderr, "error while parsing dumped file: %s\n", emsg);
        assert (pres != BOOLECTOR_PARSE_ERROR);
        (void) pstat;
        boolector_delete (tmpbtor);
        fclose (outfile);
        unlink (outfilename);
        BTOR_DELETEN (g_btorunt->mm, outfilename, flen);
      }
    }
    else if (!strcmp (tok, "dump_aiger_ascii"))
    {
      PARSE_ARGS1 (tok, int);
      boolector_dump_aiger_ascii (btor, stdout, arg1_int);
    }
    else if (!strcmp (tok, "dump_aiger_binary"))
    {
      PARSE_ARGS1 (tok, int);
      boolector_dump_aiger_binary (btor, stdout, arg1_int);
    }
    else
      btorunt_parse_error ("invalid command '%s'", tok);
  }
  g_btorunt->line++;
  len = 0;
  goto NEXT;
DONE:
  BTORUNT_LOG ("done %s", g_btorunt->filename);
  BTOR_RELEASE_STACK (arg_int);
  BTOR_RELEASE_STACK (arg_str);
  BTOR_RELEASE_STACK (sort_stack);
  BTOR_DELETEN (g_btorunt->mm, buffer, buffer_len);
  BTOR_DELETEN (g_btorunt->mm, btor_str, BTOR_STR_LEN);
  hmap_clear (hmap);
  btor_hashptr_table_delete (hmap);
  if (delete) boolector_delete (btor);
}

#ifdef BTOR_HAVE_SIGNALS
static void
exit_on_signal (int32_t sig)
{
  BTORUNT_LOG ("exit on signal %d", sig);
  raise (sig);
}
#endif

int32_t
main (int32_t argc, char **argv)
{
  int32_t i;
  uint32_t val;
  Btor *tmpbtor;
  BtorOption o;
  BtorUNTBtorOpt *btoropt;
  char *tmp;
  const char *lng;
  FILE *file;

  g_btorunt = btorunt_new ();

  for (i = 1, tmpbtor = 0; i < argc; i++)
  {
    if (!strcmp (argv[i], "-h"))
    {
      printf ("%s", BTORUNT_USAGE);
      exit (0);
    }
    else if (!strcmp (argv[i], "-v") || !strcmp (argv[i], "--verbose"))
      g_btorunt->verbosity = 1;
    else if (!strcmp (argv[i], "-e") || !strcmp (argv[i], "--exit-on-abort"))
      g_btorunt->exit_on_abort = true;
    else if (!strcmp (argv[i], "-s") || !strcmp (argv[i], "--skip-getters"))
      g_btorunt->skip = true;
    else if (!strcmp (argv[i], "-i")
             || !strcmp (argv[i], "--ignore-sat-result"))
      g_btorunt->ignore_sat = true;
    else if (!strcmp (argv[i], "-b"))
    {
      if (++i == argc) btorunt_error ("argument to '-b' missing (try '-h')");
      if (!tmpbtor) tmpbtor = boolector_new ();
      for (o = boolector_first_opt (tmpbtor), lng = 0;
           boolector_has_opt (tmpbtor, o);
           o = boolector_next_opt (tmpbtor, o))
      {
        lng = boolector_get_opt_lng (tmpbtor, o);
        if (!strcmp (lng, argv[i])) break;
      }
      if (!lng) btorunt_error ("invalid boolector option '%s'", argv[i]);
      if (++i == argc) btorunt_error ("argument to '-b' missing (try '-h')");
      val = (uint32_t) strtol (argv[i], &tmp, 10);
      if (tmp[0] != 0) btorunt_error ("invalid argument to '-b' (try -h)");
      BTOR_NEW (g_btorunt->mm, btoropt);
      btoropt->kind = o;
      btoropt->name = btor_mem_strdup (g_btorunt->mm, lng);
      btoropt->val  = val;
      BTOR_PUSH_STACK (g_btorunt->cl_btor_opts, btoropt);
    }
    else if (!strcmp (argv[i], "-d") || !strcmp (argv[i], "--dump-stdout"))
      g_btorunt->dump_stdout = true;
    else if (argv[i][0] == '-')
      btorunt_error ("invalid command line option '%s' (try '-h')", argv[i]);
    else if (g_btorunt->filename)
      btorunt_error ("multiple trace files specified (try '-h')");
    else
      g_btorunt->filename = argv[i];
  }

  if (tmpbtor) boolector_delete (tmpbtor);

  if (g_btorunt->filename)
  {
    file = fopen (g_btorunt->filename, "r");
    if (!file) btorunt_error ("can not read '%s'", g_btorunt->filename);
  }
  else
    g_btorunt->filename = "<stdin>", file = stdin;

#ifdef BTOR_HAVE_SIGNALS
  if (g_btorunt->exit_on_abort)
  {
    BTORUNT_LOG ("setting signal handlers since '-e' specified");
    signal (SIGINT, exit_on_signal);
    signal (SIGSEGV, exit_on_signal);
    signal (SIGABRT, exit_on_signal);
    signal (SIGTERM, exit_on_signal);
  }
#endif

  parse (file);
  fclose (file);
  btorunt_delete (g_btorunt);
  return 0;
}
