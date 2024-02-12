#include <iostream>
#include <chrono>
#include <unordered_map>
#include <vector>
#include "sht.h"
#include "cuckoo_hashing.h"
#include "algo_exp.h"

#define MAX_READ (100 * 1024 * 1024)

using namespace std;

KVPair kv[MAX_READ];

int load_data(const char * filename)
{
    FILE * f = fopen(filename, "rb");

    if (!f) {
        cout << filename << " not found." << endl;
    }

    fread(kv, 8, MAX_READ, f);

    return MAX_READ;
}

//ShiftingHashTable<MAX_READ, 8, 4, 100 * 1024 * 1024, 4> sht;

//void sht_test(int num)
//{
//    auto ht = &sht;
//
//    int suc_insert_num = 0;
//
//    for (int i = 0; i < num; ++i) {
//        bool result = ht->insert(kv[i].key, kv[i].val);
//        if (!result) {
//            suc_insert_num = i;
//            cout << i << " failed" << endl;
//            cout << double(i) / MAX_READ << endl;
//            break;
//        }
//    }
//
//    cout << ht->bf_element_num << endl;
//
//    // correctness check
//    bool correct = true;
//    for (int i = 0; i < suc_insert_num; ++i) {
//        uint32_t ret = ht->query(kv[i].key);
//        if (ret != kv[i].val) {
//            cout << "query error" << endl;
//            cout << ret << endl;
//            correct = false;
//            break;
//        }
//    }
//
//    if (correct) {
//        cout << "start speed test" << endl;
//        uint32_t accumulated = 0;
//
//        auto t1 = Clock::now();
//
//        constexpr int epoch = 5;
//
//        for (int k = 0; k < epoch; k++) {
//            for (int i = 0; i < suc_insert_num; ++i) {
//                uint32_t ret = ht->query(kv[i].key);
//                accumulated += ret;
//            }
//        }
//
//        auto t2 = Clock::now();
//
//        int64_t nano = chrono::nanoseconds(t2 - t1).count();
//
////        cout << nano << endl;
//        cout << "FP: " << double(ht->false_positive_probe) / (suc_insert_num * epoch) << endl;
//        cout << epoch * num / double(nano) * 1000 << "MOPS" << endl;
//        cout << accumulated << endl;
//    }
//}

void unordered_map_test(int num)
{
    unordered_map<uint32_t, uint32_t> od;

    for (int i = 0; i < num; ++i) {
        od[kv[i].key] = kv[i].val;
    }

    int accumulated = 0;
    constexpr int epoch = 1;
    auto t1 = Clock::now();
    for (int k = 0; k < epoch; k++) {
        for (int i = 0; i < num; ++i) {
            uint32_t ret = od[kv[i].key];
            accumulated += ret;
        }
    }
    auto t2 = Clock::now();

    int64_t nano = chrono::nanoseconds(t2 - t1).count();

    cout << nano << endl;
    cout << epoch * num / double(nano) * 1000 << "MOPS" << endl;

    cout << accumulated << endl;
}

int main() {
    int num = load_data("../data/000.dat");

//    sht_test(num);
    auto algos =
        vector<AlgoBase *>({
//                                   new AlgoExp<CuckooHashing<MAX_READ, 2, 2>>(),
//                                   new AlgoExp<CuckooHashing<MAX_READ, 2, 4>>(),
//                                   new AlgoExp<CuckooHashing<MAX_READ, 2, 8>>(),
                               new AlgoExp<ShiftingHashTable<MAX_READ, 8, 4, int(0.2 * 5 * 1.44 * 100 * 1024 * 1024), 5>>(),
//                               new AlgoExp<ShiftingHashTable<MAX_READ, 4, 4, 12 * 8 * 1024 * 1024, 4>>(),
//                               new AlgoExp<ShiftingHashTable<MAX_READ, 8, 16, 12 * 8 * 1024 * 1024, 4>>(),
                       });
//    unordered_map_test(num);
//    AlgoExp<ShiftingHashTable<MAX_READ, 8, 4, 12 * 8 * 1024 * 1024, 4>> r;
    for (auto algo: algos) {
        algo->set_data(kv, num);
        algo->run();
        delete algo;
    }

    return 0;
}
