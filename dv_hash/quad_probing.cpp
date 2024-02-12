#include "../xxHash/xxhash.h"
#include <limits.h>
#include <chrono>
#include <iostream>
#include <stdlib.h>
#include <fstream>
#define SEED 164178
using namespace std;

void hashing(int table[], int tsize, int arr[], int N)
{
    XXH64_hash_t seed=SEED;

    for (int i = 0; i < N; i++) {
        int hv = (int)((uint64_t) XXH64(&arr[i],4,seed) % tsize);

        if (table[hv] == -1)
            table[hv] = arr[i];
        else {
            for (int j = 0; j < tsize; j++) {
                int t = (hv + j * j) % tsize;
                if (table[t] == -1) {
                    table[t] = arr[i];
                    break;
                }
            }
        }
    }
}

void gen_input_parameters(int tablesize,int numbersize){
    int* hash_table=new int[tablesize];
    int* numbers=new int[numbersize];
    for(int i=0;i<numbersize;i++){
        numbers[i]=rand();
    }
    ofstream storage_file;
    storage_file.open ("Simple_Quad_probing_Hash.csv");
    storage_file << "inputsize,time [µs]\n";
    
    for(int loop=1;loop<13;loop++){
        memset(hash_table,-1,1024*sizeof(int));
        std::chrono::steady_clock::time_point begin = std::chrono::steady_clock::now();
        hashing(hash_table,tablesize,numbers,(2<<loop));
        std::chrono::steady_clock::time_point end = std::chrono::steady_clock::now();
        storage_file << (2<<loop)<<","<<std::chrono::duration_cast<std::chrono::microseconds>(end - begin).count()<<endl;
    }
    storage_file.close();
}

int main()
{
    gen_input_parameters(32768,8192);
    return 0;
}