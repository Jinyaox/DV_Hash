#ifndef SHIFTINGHASHTABLE17_CUCKOO_HASHING_H
#define SHIFTINGHASHTABLE17_CUCKOO_HASHING_H

#include <cstring>
#include <cstdint>
#include "simple_hash.h"

template<uint32_t max_capacity, int k, int cell_per_bucket>
class CuckooHashing
{
    constexpr static uint32_t bucket_num = max_capacity / cell_per_bucket;
    int global_counter = 123;
    struct Bucket
    {
        uint32_t key[cell_per_bucket];
        uint32_t val[cell_per_bucket];
    };

    Bucket table[bucket_num] __attribute__((aligned(64)));
public:
    CuckooHashing()
    {
        memset(table, 0, sizeof(table));
    }

    bool insert(uint32_t key, uint32_t val, int kick_remain = 5, int from_k = -1)
    {
        if (kick_remain == 0) {
            return false;
        }

        for (int i = 0; i < k; ++i) {
            uint32_t pos = hash_func[i](key) % bucket_num;
            for (int j = 0; j < cell_per_bucket; ++j) {
                if (table[pos].val[j] == 0) {
                    table[pos].key[j] = key;
                    table[pos].val[j] = val;
                    return true;
                }
            }
        }

        // try kick
        for (int i = 0; i < k; ++i) {
            uint32_t pos = hash_func[i](key) % bucket_num;
            bool flag = false;
            for (int j = 0; j < cell_per_bucket; ++j) {
                if (table[pos].key[j] == 0) {
                    flag = true;
                    break;
                }
            }
            if (flag) continue;
            for (int j = 0; j < cell_per_bucket; ++j) {
                uint32_t kick_key, kick_val;
                kick_key = table[pos].key[j];
                kick_val = table[pos].val[j];
                if (kick_key == 0) continue;
                table[pos].key[j] = 0;
                if (insert(kick_key, kick_val, kick_remain - 1)) {
                    table[pos].key[j] = key;
                    table[pos].val[j] = val;
                    return true;
                }
                table[pos].key[j] = kick_key;
            }
        }

        return false;
    }

    uint32_t query(uint32_t key)
    {
        for (int i = 0; i < k; ++i) {
            uint32_t pos = hash_func[i](key) % bucket_num;
            for (int j = 0; j < cell_per_bucket; ++j) {
                if (table[pos].key[j] == key) {
                    if (table[pos].val[j] == 0) {
                        cout << "wtf" << endl;
                    }
                    return table[pos].val[j];
                }
            }
        }

        return 0;
    }

    void report() {}
};


#endif //SHIFTINGHASHTABLE17_CUCKOO_HASHING_H
