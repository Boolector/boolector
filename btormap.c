#include "btormap.h"

/*------------------------------------------------------------------------*/

BtorNodeMap*
btor_new_node_map (Btor* btor)
{
  assert (btor);
  return btor_new_ptr_hash_table (btor->mm,
                                  (BtorHashPtr) btor_hash_exp_by_id,
                                  (BtorCmpPtr) btor_compare_exp_by_id);
}

void
btor_delete_node_map (Btor* btor, BtorNodeMap* map)
{
  BtorPtrHashBucket* bucket;
  assert (btor);
  assert (map);
  for (bucket = map->first; bucket; bucket = bucket->next)
  {
    btor_release_exp (btor, bucket->key);
    btor_release_exp (btor, bucket->data.asPtr);
  }
}

BtorNode*
btor_mapped_node (BtorNodeMap* map, BtorNode* node)
{
  BtorPtrHashBucket* bucket = btor_find_in_ptr_hash_table (map, node);
  if (!bucket) return 0;
  assert (bucket->key == node);
  return bucket->data.asPtr;
}

void
btor_map_node (Btor* btor, BtorNodeMap* map, BtorNode* src, BtorNode* dst)
{
  BtorPtrHashBucket* bucket;
  assert (btor);
  assert (map);
  assert (src);
  assert (dst);
  assert (!btor_find_in_ptr_hash_table (map, src));
  bucket = btor_insert_in_ptr_hash_table (map, src);
  assert (bucket);
  assert (bucket->key == src);
  bucket->key = btor_copy_exp (btor, src);
  assert (!bucket->data.asPtr);
  bucket->data.asPtr = btor_copy_exp (btor, dst);
}
