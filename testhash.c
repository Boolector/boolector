#include "testhash.h"
#include "btorhash.h"

#ifdef NDEBUG
#undef NDEBUG
#endif

#include <assert.h>

static BtorMemMgr *mem;

void
init_hash_tests (void)
{
  mem = btor_new_mem_mgr ();
}

void
run_hash_tests (int argc, char **argv)
{
}

void
finish_hash_tests (void)
{
  btor_delete_mem_mgr (mem);
}
