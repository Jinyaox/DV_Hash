#include <iostream>
#include <ctime>
#include <cstdlib>
#include <vector>
#include "../xxHash/xxhash.h"
#include <cmath>

using namespace std;

typedef struct hash_store{
    uint8_t active;
    uint64_t m_sum;
    uint64_t sum_without_i;
}hash_store;


class CuckooHash{
private:  
    int lnBucket;   //size of bucket  
    uint64_t verifier;
    uint64_t mask;
    hash_store *mpKeyBucket1;  //the first bucket for first hash  
    hash_store *mpKeyBucket2;  //the second bucket for second hash  
    XXH64_hash_t seed1;
    XXH64_hash_t seed2;
    const static int MaxLoop = 1000;  //used to control rehash loop  
    int lnCantInsertNum;  
  
private:  
    //first hash function  
    int hHashOne(int value)  
    {
        int position=(uint64_t)XXH64(&value,8,seed1) % lnBucket;
        return position;
    }  
  
    //second hash function  
    int hHashTwo(int value)  
    {  
        int position=(uint64_t)XXH64(&value,8,seed2) % lnBucket;
        return position;
    }  

  
    //todo: juge one num is Prime NUM or not  
    bool hIsPrime(int inN)  
    {  
        if(inN <= 0) return false;  
  
        int last = sqrt((double)inN);  
  
        for(int i = 2; i<= last; i++)  
        {  
            if(inN % i == 0)  
                return false;  
        }  
  
        return true;  
    }  
    int hGetMinPrime(int inNum)  
    {  
        while( !hIsPrime(inNum) ) inNum ++;  
  
        return inNum;   
    }  
  
    //try to rehash all the other key  
    int hReHash(uint64_t iKey, uint64_t M_without_i, int deeps, short loc)  
    {
        //ikey == msum ^ seed ^ mask
        //returns the location of storage, just in case of reverting
        uint64_t outKey= iKey ^ seed1 ^ mask ^ verifier;

        if(deeps <= 0) {
            lnCantInsertNum++;
            return -1;  
        }

        int lHashKey1 = hHashOne(outKey);  
        int lHashKey2 = hHashTwo(outKey);  
  
        if(loc==1) 
        {  
            if(mpKeyBucket2[lHashKey2].active==0)  
            {  
                mpKeyBucket2[lHashKey2].m_sum = iKey;
                mpKeyBucket2[lHashKey2].sum_without_i=M_without_i;
                mpKeyBucket2[lHashKey2].active=1;
                return lHashKey2;  
            }  // 第一个槽有元素，第二个槽空
            else  
            {  
                if( hReHash(mpKeyBucket2[lHashKey2].m_sum,mpKeyBucket2[lHashKey2].sum_without_i, deeps - 1, 2)>=0)  
                {   
                    mpKeyBucket2[lHashKey2].m_sum = iKey;
                    mpKeyBucket2[lHashKey2].sum_without_i=M_without_i;
                    mpKeyBucket2[lHashKey2].active=1; 
                    return lHashKey2;  
                }  //递归寻找空槽    
                else{
                    return -1;
                }                  
            }  
        }  
        else
        {  
            if(mpKeyBucket1[lHashKey1].active==0)//series   
            {  
                mpKeyBucket1[lHashKey1].m_sum = iKey;
                mpKeyBucket1[lHashKey1].sum_without_i=M_without_i;
                mpKeyBucket1[lHashKey1].active=1;  
                return lHashKey1;  
            }  
            else  
            {  
                if( hReHash(mpKeyBucket1[lHashKey1].m_sum,mpKeyBucket1[lHashKey1].sum_without_i, deeps - 1, 1)>=0)  
                {   
                    mpKeyBucket1[lHashKey1].m_sum = iKey;
                    mpKeyBucket1[lHashKey1].sum_without_i=M_without_i;
                    mpKeyBucket1[lHashKey1].active=1;  
                    return lHashKey1;  
                }  //递归寻找空槽    
                else{
                    return -1;
                } 
            }  
        }  
  
        return -1;  
  
    }  
  
public:  
    CuckooHash(int inNum,XXH64_hash_t input_seed1,XXH64_hash_t input_seed2,uint64_t verifier, uint64_t secret_mask)  
    {  
        lnBucket = inNum;  
  
        mpKeyBucket1 = NULL;  
  
        mpKeyBucket2 = NULL; 

        lnCantInsertNum = 0;   
        
        this->seed1=input_seed1;
        this->seed2=input_seed2;
        this->verifier=verifier;
        this->mask=secret_mask;
    }

    void InitHashTable()  
    {  
        lnBucket = hGetMinPrime(lnBucket); //哈希槽的容量取质数，可以避免位失效 

        mpKeyBucket1 = new hash_store[lnBucket];  //给分配的槽位置0
          
        mpKeyBucket2 = new hash_store[lnBucket];  
          
    }  
  
    ~CuckooHash()  
    {  
        if(mpKeyBucket1)  
            delete[] mpKeyBucket1;  
  
        if(mpKeyBucket2)  
            delete[] mpKeyBucket2;  
    }  
  
    int Insert(uint64_t iKey, uint64_t M_without_i,short* table)  
    {  
        int rehash_position=-1; //we are initializing the variable for now
        int loc=find(iKey,table);
        if(loc!=-1) return loc;  
  
        int lHashKey1 = hHashOne(iKey);  
        int lHashKey2 = hHashTwo(iKey);  
  
        if(mpKeyBucket1[lHashKey1].active==0){
            mpKeyBucket1[lHashKey1].active=1;
            mpKeyBucket1[lHashKey1].m_sum=iKey^seed1^mask^verifier;
            mpKeyBucket1[lHashKey1].sum_without_i=M_without_i;
            *table=1;
            return lHashKey1;
        }  
        else if(mpKeyBucket2[lHashKey2].active==0){
            mpKeyBucket2[lHashKey2].active=1;
            mpKeyBucket2[lHashKey2].m_sum=iKey^seed1^mask^verifier;
            mpKeyBucket2[lHashKey2].sum_without_i=M_without_i;
            *table=2;
            return lHashKey2;
        }
        else  
        {  
            rehash_position=hReHash(mpKeyBucket1[lHashKey1].m_sum,mpKeyBucket1[lHashKey1].sum_without_i, MaxLoop,1);
            if(rehash_position>=0){
                mpKeyBucket1[lHashKey1].active=1;
                mpKeyBucket1[lHashKey1].m_sum=iKey^seed1^mask^verifier;
                mpKeyBucket1[lHashKey1].sum_without_i=M_without_i;
                *table=1;
                return lHashKey1;
            }
            else{
                rehash_position=hReHash(mpKeyBucket2[lHashKey2].m_sum,mpKeyBucket2[lHashKey2].sum_without_i, MaxLoop,2);
                if(rehash_position>=0){
                    mpKeyBucket2[lHashKey2].active=1;
                    mpKeyBucket2[lHashKey2].m_sum=iKey^seed1^mask^verifier;
                    mpKeyBucket2[lHashKey2].sum_without_i=M_without_i;
                    *table=2;
                    return lHashKey2;
                }
            }
        }
        return -1;
    }

    hash_store* retrieve(uint64_t outkey){
        short table=5;
        int loc=find(outkey,&table);
        if(loc!=-1){
            switch (table)
            {
            case 1:
                return &mpKeyBucket1[loc];
            
            default:
                return &mpKeyBucket2[loc];
            }
        }
        return NULL;
    }

    bool remove(int table_idx,int loc){
        switch (table_idx)
            {
            case 1:
                mpKeyBucket1[loc].active=0;
                return true;
            
            default:
                mpKeyBucket2[loc].active=0;
                return true;
            }
        return false;
    }

    int find(uint64_t irKey, short* table=NULL)
    {  
        //irkey is the outkey
        int lHashKey1 = hHashOne(irKey);
        uint64_t comparee=mpKeyBucket1[lHashKey1].m_sum^seed1^mask;
        if((mpKeyBucket1[lHashKey1].active==1)&&((comparee^irKey)==verifier)){
            if(table!=NULL){
                *table=1;
            }
            return lHashKey1; 
        } 
  
        int lHashKey2 = hHashTwo(irKey);  
        comparee=mpKeyBucket2[lHashKey2].m_sum^seed1^mask;
        if((mpKeyBucket2[lHashKey2].active==1)&&((comparee^irKey)==verifier)){
            if(table!=NULL){
                *table=2;
            }
            return lHashKey2;
        } 
        return -1;  
    }
};