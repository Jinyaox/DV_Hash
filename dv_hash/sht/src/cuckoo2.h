#ifndef SHIFTINGHASHTABLE17_CUCKOO2_H
#define SHIFTINGHASHTABLE17_CUCKOO2_H

#include <stdint-gcc.h>
#include <cstring>
#include "BOB_hash.h"
#include "simple_hash.h"
#include <iostream>
#include <algorithm>
#ifdef __MSC_VER
#include <intrin.h>
#else
#include <x86intrin.h>  // Not just <immintrin.h> for compilers other than icc
#endif

//#define __rorq(X, Y) (X) * (Y)

using namespace std;

uint32_t (*prefer_hash)(uint32_t) = multiplicative0;

template<uint32_t max_capacity, uint32_t d, uint32_t cell_per_bucket, uint32_t bf_size_in_bits, uint32_t bf_k>
class Cuckoo2
{
    static constexpr uint32_t bucket_per_subtable = max_capacity / d / cell_per_bucket;
    // suppose key size and value size if 4 bytes
    struct Bucket
    {
        uint32_t key[cell_per_bucket];
        uint32_t val[cell_per_bucket];
    };
//public:
    Bucket subtables[d][bucket_per_subtable] __attribute__((aligned(64)));

    uint64_t bf[(bf_size_in_bits + 63 + d) / 64];
    uint8_t cbf[bf_size_in_bits + d];


    uint32_t get_home_table(uint32_t key)
    {
        return prefer_hash(key) % d;
    }

    uint32_t get_subtable_position(uint32_t key, uint32_t idx)
    {
        return hash_func[idx](key) % bucket_per_subtable;
    }

    void insert_into_bf(uint32_t key, uint32_t idx)
    {
        bf_element_num++;
        for (int i = 0; i < bf_k; ++i) {
            uint32_t pos = hash_func[i](key) % bf_size_in_bits;
            uint32_t bucket = pos / 64;
            uint32_t offset = (pos + idx) % 64;
            cbf[bucket * 64 + offset]++;
            bf[bucket] |= (1ull << offset);
        }
    }

    void remove_from_bf(uint32_t key, uint32_t idx)
    {
        bf_element_num--;
        for (int i = 0; i < bf_k; ++i) {
            uint32_t pos = hash_func[i](key) % bf_size_in_bits;
            uint32_t bucket = pos / 64;
            uint32_t offset = (pos + idx) % 64;
            cbf[bucket * 64 + offset]--;
            if (cbf[bucket * 64 + offset] == 0) {
                bf[bucket] &= ~(1ull << offset);
            }
        }
    }

    uint32_t query_bf(uint32_t key)
    {
        uint32_t ret = (~0u);
        for (int i = 0; i < bf_k; ++i) {
            uint32_t pos = hash_func[i](key) % bf_size_in_bits;
            uint32_t bucket = pos / 64;
            uint32_t offset = pos % 64;
            uint64_t bt = bf[bucket];
//
//            cout << ret << " " << __rorq(bt, offset) << endl;
            ret &= __rorq(bt, offset);
        }
        return ret;
    }

public:
    int bf_element_num;
    int false_positive_probe;

    Cuckoo2() {
        memset(subtables, 0, sizeof(subtables));
        memset(bf, 0, sizeof(bf));
        bf_element_num = 0;
        false_positive_probe = 0;
    }

    bool insert(uint32_t key, uint32_t val, int kick_remain = 5, bool from_home = false)
    {
        if (kick_remain == 0) {
            return false;
        }

        // try insert into home table
        uint32_t prefer_table = get_home_table(key);
        Bucket & prefer_b = subtables[prefer_table][get_subtable_position(key, prefer_table)];
        for (int k = 0; k < cell_per_bucket; ++k) {
            if (prefer_b.key[k] == 0) {
                prefer_b.key[k] = key;
                prefer_b.val[k] = val;
                return true;
            }
        }

        // if cannot, insert to abroad table
        // and insert it into the bf
        for (int i = 1; i < d; ++i) {
            uint32_t idx = (i + prefer_table) % d;
            uint32_t pos = get_subtable_position(key, idx);
            Bucket & b = subtables[idx][pos];
            for (int k = 0; k < cell_per_bucket; ++k) {
                if (b.key[k] == 0) {
                    b.key[k] = key;
                    b.val[k] = val;
                    // TODO Insert into bf
                    insert_into_bf(key, idx);
                    return true;
                }
            }
        }

        if (from_home) {
            return false;
        }

        // if others are failed too
        // find an abroad element kick it
        for (int k = 0; k < cell_per_bucket; ++k) {
            uint32_t other_key = prefer_b.key[k];
            uint32_t other_prefer_table = get_home_table(other_key);
            if (other_prefer_table != prefer_table) {
//                cout << "kick occur " << prefer_table << " " << other_prefer_table << endl;
                uint32_t other_val = prefer_b.val[k];
                bool result = insert(other_key, other_val, kick_remain - 1);
                if (result) {
                    prefer_b.key[k] = key;
                    prefer_b.val[k] = val;
                    // TODO remove old key from bf
                    remove_from_bf(other_key, prefer_table);
                    return true;
                }
            }
        }

        // else find an home element and kick it
        uint32_t start_idx = key % cell_per_bucket;
        for (int t = 0; t < cell_per_bucket; ++t) {
            uint32_t k = (t + start_idx) % cell_per_bucket;
            uint32_t other_key = prefer_b.key[k];
//            cout << "kick occur " << endl;
            uint32_t other_val = prefer_b.val[k];
            bool result = insert(other_key, other_val, kick_remain - 1, true);
            if (result) {
                prefer_b.key[k] = key;
                prefer_b.val[k] = val;
                return true;
            }
        }

        // if the kick operation failed
        // throw an insertion error
        return false;
    }

    bool query_bucket(Bucket & b, uint32_t key, uint32_t & ret)
    {
        if (cell_per_bucket == 4) {
            __m128i simd_key = _mm_set1_epi32(key);
            __m128i ra = _mm_cmpeq_epi32(*(__m128i *)b.key, simd_key);
            int pos = _mm_movemask_ps(*(__m128*)&ra);
            if (!pos) {
                return false;
            } else {
                int k = _tzcnt_u32(pos);
                ret = b.val[k];
                return true;
            }
        }
//        else if (cell_per_bucket == 8) {
//            __m128i simd_key = _mm_set1_epi32(key);
//            __m128i ra = _mm_cmpeq_epi32(*(__m128i *)b.key, simd_key);
//            __m128i rb = _mm_cmpeq_epi32(*(__m128i *)(b.key + 4), simd_key);
//            int pos = (_mm_movemask_ps(*(__m128*)&rb) << 4) + _mm_movemask_ps(*(__m128*)&ra);
//            if (!pos) {
//                return false;
//            } else {
//                int k = _tzcnt_u32(pos);
//                ret = b.val[k];
//                return true;
//            }
//        }
        else {
            for (int k = 0; k < cell_per_bucket; ++k) {
                if (b.key[k] == key) {
                    ret = b.val[k];
                    return true;
                }
            }
        }

        return false;
    }

    uint32_t query(uint32_t key)
    {
        uint32_t mask = query_bf(key);
        uint32_t ret = 0;


        return 0;
    }

    void report()
    {
        cout << "FP_PROBE: " << false_positive_probe << endl;
        cout << "ABROAD_CNT: " << bf_element_num << endl;
    }
} __attribute__((aligned(64)));

#endif //SHIFTINGHASHTABLE17_CUCKOO2_H
