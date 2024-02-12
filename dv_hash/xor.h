#include <iostream>
#include <stdlib.h>
using namespace std;

int gen_rand(int rand[],int n){
    /*
    generate n random numbers that XOR's to 0
    */
   int current=0;
   for (int i=0;i<n-1;i++){
    rand[i]=std::rand();
    current=current^rand[i];
   }
   rand[n-1]=current;
   return current ^ rand[n-1];
}

uint64_t concat_coord(int x, int y){
    return (uint64_t) x << 32 | y;
} 

uint64_t get_hashed_share(uint64_t priviate_key, uint64_t coordinate){
    return coordinate ^ priviate_key;
}

uint64_t gen_party_indexes(int hash_index[], int party_num){ //100100 means party 5, 2 are present
    //the parties give its indexes
    uint64_t result=0;
    int debug;
    for(int i=0;i<party_num;i++){
        debug=hash_index[i];
        if(debug!=-1){
            result |= 1<<debug; //now we get the bit mapping
        }
    }
    return result;
}

uint64_t gen_sum_m(uint64_t m[],int party_num){
    uint64_t result=0;
    for(int i=0;i<party_num;i++){
        result^=m[i];
    }
    return result;
}