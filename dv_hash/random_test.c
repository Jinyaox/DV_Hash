#include "time.h"
#include "string.h"
#include "stdio.h"
#include "stdlib.h"
#include <time.h>
#include "/Users/rudolphtorres/Desktop/xxHash/xxhash.h"
#define SPACE 1024
#define DEGREE 4
#define START 31
#define TOTAL_TEST 16384

// void base_performance(){
//     int space[SPACE];
//     memset(space,0,1024*sizeof(int));
//     for(int i=0;i<TOTAL_TEST;i++){
//         space[rand()%SPACE]++;
//     }
// }

// clang -std=gnu99 random_test.c /Users/rudolphtorres/Desktop/xxHash/libxxhash.0.8.2.dylib -o StarMeals

void twoWise(){
    FILE *fptr;
    fptr = fopen("twoWise.csv", "w");

    int space[1024];
    memset(space,0,SPACE*sizeof(int));

    int p1=101; int p2=148;

    clock_t start = clock(), diff;
    for(int i=0;i<TOTAL_TEST;i++){
        space[(p2*i+p1)%SPACE]++;
    }
    diff = clock() - start;

    printf("Avg Time taken %d miliseconds for TWO WISE\n", (int) diff);

    for(int i=0;i<SPACE;i++){
        fprintf(fptr,"%d,%d\n",i, space[i]);
    }
    fclose(fptr);
}

void xxh_performance(){
    FILE *fptr;
    fptr = fopen("xxh.csv", "w");
    
    int space[1024];
    memset(space,0,SPACE*sizeof(int));
    XXH64_hash_t seed=(XXH64_hash_t) 101;

    clock_t start = clock(), diff;
    for(int i=0;i<TOTAL_TEST;i++){
        space[((unsigned)XXH32(&i,4,seed))%SPACE]++;
    }
    diff = clock() - start;

    printf("Avg Time taken %d miliseconds for XXH\n", (int) diff);

    for(int i=0;i<SPACE;i++){
        fprintf(fptr,"%d,%d\n",i, space[i]);
    }
    fclose(fptr);
}

int main(){
    xxh_performance(); //this has better randomness 
    twoWise();
}