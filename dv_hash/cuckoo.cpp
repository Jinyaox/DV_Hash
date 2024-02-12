#include "cuckoo.h"
#include "../xxHash/xxhash.h"
#include <limits.h>
#include <chrono>
#include <iostream>
#include <stdlib.h>
#define TABLE_SIZE 1024

int main(){
    XXH64_hash_t seed1 =(XXH64_hash_t) rand();
    XXH64_hash_t seed2 =(XXH64_hash_t) rand();
    uint64_t index_key=(uint64_t)rand()<<32|rand();
    uint64_t verifier=(uint64_t)rand()<<32|rand();
    CuckooHash* table=new CuckooHash(TABLE_SIZE,seed1,seed2,verifier,index_key);
    table->InitHashTable();

    for(int loop=1;loop<11;loop++){
        std::chrono::steady_clock::time_point begin = std::chrono::steady_clock::now();
        short tab=0;
        for(int i=0;i<(2<<loop);i++){
            uint64_t out=(uint64_t)rand()<<32|rand();
            uint64_t out2=(uint64_t)rand()<<32|rand();
            table->Insert(out,out2,&tab);
        }
        std::chrono::steady_clock::time_point end = std::chrono::steady_clock::now();
        std::cout << "Time difference for " << (2<<loop) << " = " << std::chrono::duration_cast<std::chrono::microseconds>(end - begin).count() << "[µs]" << std::endl;
    }
}