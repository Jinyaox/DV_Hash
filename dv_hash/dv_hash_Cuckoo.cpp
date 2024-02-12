#include <iostream>
#include <stdlib.h>
#include "crt.h"
#include "xor.h"
#include "helper.h"
#include "cuckoo.h"
#include "../xxHash/xxhash.h"
#include <limits.h>
#include <chrono>
#include <fstream>
using namespace std;

//compile with clang++ dv_hash_Cuckoo.cpp ../xxHash/libxxhash.0.8.2.dylib -o dv_cuckoo
// do not compile with O optimization flag

int conflict_ctr=0;
long counter=0;
short deactivate=1;
long memory_counter=0;

typedef struct receipt{
    uint64_t bitmap;
    uint64_t outkey;
}receipt;

typedef struct storage_info{
    short table;
    int location;
    int which_table;
}storage_info;


class prime_hashes{
    public:
    
    int* primes;
    int* lock;
    int size;


    prime_hashes(unsigned size, unsigned starting=2){
        this->size=size;
        this->primes= new int[size];
        this->lock=new int[size];
        memset(this->lock,0,size*sizeof(short));
        gen_n_primes(size,this->primes,starting);
    }

    short can_gen(int indexes[], uint64_t value, int parties){
        uint64_t result=1;
        int idx=0;
        for(int i=0;i<parties;i++){
            idx=indexes[i];
            if(idx!=-1){
                result=result*primes[idx];
                if(result>=value){
                    return 1; //(ok)
                }
            }
        }
        return 0;
    }

    short locked(int index){
        return this->lock[index]==1;
    }

    void clear_lock(){
        //clear all locks in this thing
        memset(this->lock,0,this->size*sizeof(int));
    }

    int largest(){
        return this->primes[size-1];
    }

    ~prime_hashes(){
        delete[] this->primes;
        delete[] this->lock;
    }
};

class node{
    public:
    uint64_t index_key; //the mask thing for m1 m2 m3 hash (a mask)
    uint64_t verifier;
    short ID;
    int place;
    int prime_size;
    CuckooHash* all_tables[10];
    XXH64_hash_t seed1;
    XXH64_hash_t seed2;

    node(){
        seed1 =(XXH64_hash_t) rand();
        seed2 =(XXH64_hash_t) rand();
    }

    void init(int table_size, int p_size, short id, uint64_t verifier){
        this->ID=id;
        this->index_key=(uint64_t)rand()<<32|rand();
        prime_size=p_size;
        this->verifier=verifier;
        
        //implmenting the conflict resolution 
        for(int i=0;i<10;i++){
            all_tables[i]=new CuckooHash(table_size,seed1,seed2,verifier,index_key);
            all_tables[i]->InitHashTable();
        }
    }

    int eval(int val,int max_prime){
        return (int)((uint64_t) XXH64(&val,4,seed1) % max_prime);
    }

    int store(uint64_t out_key, uint64_t sum_m, uint64_t m,short* tab,int* location){
        int current=0;
        while(current<10){
            int res=all_tables[current]->Insert(out_key,sum_m^m,tab)==-1;
            if(res==-1){
                current++;
            }
            else{
                *location=current;
                memory_counter++;
                return res;
            }
        }
        return -1;
    }

    short retrieve(uint64_t out_key, uint64_t index, int prime_remainder_pair[]){
        //store the result in prime remainder pair if valid, else return 0

        uint64_t mask=((uint64_t)1)<<this->ID;
        if((index&mask)==0){return 0;} //not your turn
        int current=0;
        hash_store* res=NULL;
        while(current<10){
            res=all_tables[current]->retrieve(out_key);
            if(res==NULL){
                current++;
            }
            else{
                break;
            }
        }

        if (current<10){
            hash_store result=*res;
            uint64_t piri=result.m_sum^seed1^result.sum_without_i; //this contains a bug
            prime_remainder_pair[0]=piri>>32;
            prime_remainder_pair[1]=piri & 0x00000000FFFFFFFF;
            return 1;
        }
        return 0;
    }

    uint64_t add(uint64_t out_key, uint64_t index, uint32_t val){
        uint64_t mask=((uint64_t)1)<<this->ID;
        if((index&mask)==0){return 0;} //not your turn
        hash_store* res=NULL;
        int current=0;
        while(current<10){
            res=all_tables[current]->retrieve(out_key);
            if(res==NULL){
                current++;
            }
            else{
                break;
            }
        }

        if (current<10){
            hash_store result=*res;
            memset(res,0,sizeof(hash_store));
            uint64_t piri=result.m_sum^seed1^result.sum_without_i;
            uint64_t prime=piri>>32;
            uint64_t remainder=piri & 0x00000000FFFFFFFF;
            remainder=(remainder+val)%prime;
            piri=(prime<<32|remainder);
            return piri ^ index_key;
        }
        return 0;
    }

    uint64_t gen_m(prime_hashes* ph, int idx, uint64_t val){
        uint64_t prime=ph->primes[idx];
        uint64_t remainder=val%prime;
        uint64_t piri=(prime<<32|remainder);
        uint64_t res=piri ^ index_key;
        return res;
    }

    void remove(int table_idx,int loc, int which_table){
        all_tables[which_table]->remove(table_idx-1,loc);
    }

    ~node(){
        for(int i=0;i<10;i++){
            delete all_tables[i];
        }
    }
};



class dv_hash{
    
    private:
    node* parties;
    prime_hashes* ph;
    uint64_t verify_key;

    public:

    dv_hash(int parties, int degree=3){
        ph=new prime_hashes(256);
        this->parties= new node[parties];
        verify_key=(uint64_t)rand()<<32|rand();
        for(int i=0;i<parties;i++){
            this->parties[i].init(16384,256,i,verify_key);
        }
    }

    void revert(storage_info* storage){
        node* current;
        for(int i=0;i<64;i++){
            if((storage[i].table!=0)&&(storage[i].location!=0)){
                current=&this->parties[i];
                current->remove(storage[i].table,storage[i].location,storage[i].which_table);
            }
        }
    }

    short store(uint64_t bitmap, uint64_t val, uint64_t result[2]){
        int hash_index[64];
        int collision[64];

        memset(collision,-1,64*sizeof(int));
        memset(hash_index,-1,64*sizeof(int));
        ph->clear_lock();
        node* current;
        int id;
        for(int i=0;i<64;i++){
            if ((uint64_t)1<<i & bitmap) {
                current=&(this->parties[i]);
                id=current->eval(val,256);
                if(ph->lock[id]!=1){
                    hash_index[i]=id;
                    ph->lock[id]=1;
                }
                else{
                    collision[i]=id;
                }
            }
        }

        int place=0; //the iterator for the normal parties (use this first)
        int collision_substitute=0; //iterator for substituting party
        int current_idx;
        int debug=0;
        int revert=0; //make sure clear it

        while(ph->can_gen(hash_index,val,64)==0){ //see if the current hash indexes are sufficiently large

            if(place>=64){ 
                //conflict_ctr++;
                debug = collision[collision_substitute];

                while(debug==-1){ //find the next 

                    //the if condition checks if we used all possible values
                    if(collision_substitute>=64){
                        return 0; //cannot do it sadly
                    }

                    collision_substitute++;
                    debug=collision[collision_substitute];
                }
                hash_index[collision_substitute]=debug;
                
                while((ph->lock[hash_index[collision_substitute]]==1)&&(hash_index[collision_substitute]<(ph->size)-1)){
                    hash_index[collision_substitute]++;
                }
                ph->lock[hash_index[collision_substitute]]=1;
                collision_substitute++;

            }
            else{
                ph->lock[hash_index[place]]=0;
                revert=hash_index[place];
                hash_index[place]++;
                conflict_ctr++;

                while((ph->lock[hash_index[place]]==1)&&(hash_index[place]<(ph->size)-1)){
                    hash_index[place]++;
                }

                if((hash_index[place]>=ph->size)){
                    ph->lock[revert]=1;
                    hash_index[place]=revert;
                    place++;
                }else{
                    ph->lock[hash_index[place]]=1;
                }
                
                while(hash_index[place]==-1){ //move to the next place for hash index
                    if(place>=64){
                        break;
                    }
                    else{
                        place++;
                    }
                }
            }
        }

        uint64_t all_m [64];
        int final_party[64];

        memset(all_m,0,sizeof(uint64_t)*64);
        memset(final_party,-1,sizeof(int)*64);

        //fix this up
        for(int i=0;i<64;i++){
            if ((uint64_t)1<<i & bitmap){
                current=&this->parties[i];//get the party associated with it
                if(hash_index[i]>=0){
                    current_idx=hash_index[i];
                    final_party[i]=i; //get the final party size and nodes;
                }
                else{
                    continue;
                }
                all_m[i]=current->gen_m(ph,current_idx,val);
            }
        }
        deactivate=1;

        uint64_t sum_m=gen_sum_m(all_m,64);

        storage_info* storage=new storage_info[64];
        //check if individual hash table has issues 
        for(int i=0;i<64;i++){
            if ((uint64_t)1<<i & bitmap){
                current=&this->parties[i]; //get the party associated with it 
                storage[i].location=current->store(sum_m^verify_key,sum_m,all_m[i],&storage[i].table,&storage[i].location); 

                if(storage[i].location==-1){
                    this->revert(storage);
                    delete[] storage;
                    return -1;
                }
            }
            //else continue the next loop, the party is not being used yet
        }
    
        result[0]= gen_party_indexes(final_party,64); 
        result[1]= sum_m ^ verify_key;

        delete[] storage;
        return 1;
    }

    uint64_t store_no_change(uint64_t bitmap, uint64_t val){
        int hash_index[64];
        int collision[64];

        memset(collision,-1,64*sizeof(int));
        memset(hash_index,-1,64*sizeof(int));
        ph->clear_lock();
        node* current;
        int id;
        std::chrono::steady_clock::time_point begin = std::chrono::steady_clock::now();
        for(int i=0;i<64;i++){
            if ((uint64_t)1<<i & bitmap) {
                current=&(this->parties[i]);
                id=current->eval(val,256);
                if(ph->lock[id]!=1){
                    hash_index[i]=id;
                    ph->lock[id]=1;
                }
                else{
                    collision[i]=id;
                }
            }
        }

        int place=0; //the iterator for the normal parties (use this first)
        int collision_substitute=0; //iterator for substituting party
        int current_idx;
        int debug=0;
        int revert=0; //make sure clear it

        while(ph->can_gen(hash_index,val,64)==0){ //see if the current hash indexes are sufficiently large

            if(place>=64){ 
                debug = collision[collision_substitute];

                while(debug==-1){ //find the next 

                    //the if condition checks if we used all possible values
                    if(collision_substitute>=64){
                        return 0; //cannot do it sadly
                    }

                    collision_substitute++;
                    debug=collision[collision_substitute];
                }
                hash_index[collision_substitute]=debug;
                
                while((ph->lock[hash_index[collision_substitute]]==1)&&(hash_index[collision_substitute]<(ph->size)-1)){
                    hash_index[collision_substitute]++;
                }
                ph->lock[hash_index[collision_substitute]]=1;
                collision_substitute++;

            }
            else{
                ph->lock[hash_index[place]]=0;
                revert=hash_index[place];
                hash_index[place]++;
                conflict_ctr++;

                while((ph->lock[hash_index[place]]==1)&&(hash_index[place]<(ph->size)-1)){
                    hash_index[place]++;
                }

                if((hash_index[place]>=ph->size)){
                    ph->lock[revert]=1;
                    hash_index[place]=revert;
                    place++;
                }else{
                    ph->lock[hash_index[place]]=1;
                }
                
                while(hash_index[place]==-1){ //move to the next place for hash index
                    if(place>=64){
                        break;
                    }
                    else{
                        place++;
                    }
                }
            }
        }
        std::chrono::steady_clock::time_point end = std::chrono::steady_clock::now();
        counter+=std::chrono::duration_cast<std::chrono::microseconds>(end - begin).count();

        uint64_t all_m [64];

        memset(all_m,0,sizeof(uint64_t)*64);

        //fix this up
        for(int i=0;i<64;i++){
            if ((uint64_t)1<<i & bitmap){
                current=&this->parties[i];//get the party associated with it
                if(hash_index[i]>=0){
                    current_idx=hash_index[i];
                }
                else{
                    current_idx=collision[i];
                }
                std::chrono::steady_clock::time_point begin = std::chrono::steady_clock::now();
                all_m[i]=current->gen_m(ph,current_idx,val);
                std::chrono::steady_clock::time_point end = std::chrono::steady_clock::now();
                if(deactivate==1){
                    counter+=std::chrono::duration_cast<std::chrono::microseconds>(end - begin).count();
                    deactivate=0;
                }
            }
        }
        deactivate=1;

        begin = std::chrono::steady_clock::now();
        uint64_t sum_m=gen_sum_m(all_m,64);
        end = std::chrono::steady_clock::now();
        counter+=std::chrono::duration_cast<std::chrono::microseconds>(end - begin).count();

        storage_info* storage=new storage_info[64];
        //check if individual hash table has issues 
        for(int i=0;i<64;i++){
            if ((uint64_t)1<<i & bitmap){
                current=&this->parties[i]; //get the party associated with it 
                begin = std::chrono::steady_clock::now();
                storage[i].location=current->store(sum_m^verify_key,sum_m,all_m[i],&storage[i].table,&storage[i].location); 
                end = std::chrono::steady_clock::now();  
                if(deactivate==1){
                    counter+=std::chrono::duration_cast<std::chrono::microseconds>(end - begin).count();
                    deactivate=0;
                }
                if(storage[i].location==-1){
                    this->revert(storage);
                    delete[] storage;
                    return -1;
                }
            }
        }
        deactivate=1;

        delete[] storage;
        return sum_m ^ verify_key;
    }

    //needs to fix this
    uint64_t retrieve(uint64_t parties, uint64_t out_key){
        int value_storage[]={0,0};
        uint64_t primes[64],remainder[64];
        int ctr=0; uint64_t lcm=1; uint64_t OLD_lcm=1; //prevent LCM overflow
        for(int i=0;i<64;i++){
            std::chrono::steady_clock::time_point begin = std::chrono::steady_clock::now();
            int res=this->parties[i].retrieve(out_key,parties,value_storage);
            std::chrono::steady_clock::time_point end = std::chrono::steady_clock::now();
            if(res==1){
                if (deactivate==1){
                    counter+=std::chrono::duration_cast<std::chrono::microseconds>(end - begin).count();
                    deactivate=0;
                }
                remainder[ctr]=value_storage[1]; 
                primes[ctr]=value_storage[0]; 
                ctr++;
            }
        }
        std::chrono::steady_clock::time_point begin = std::chrono::steady_clock::now();
        uint64_t result=CRT(primes,remainder,ctr);
        std::chrono::steady_clock::time_point end = std::chrono::steady_clock::now();
        counter+=std::chrono::duration_cast<std::chrono::microseconds>(end - begin).count();
        deactivate=1;

        return result;
    }

    int add(uint64_t parties, uint64_t& out_key, uint32_t operand){
        uint64_t result=0;
        uint64_t m_temp[64]; memset(m_temp,0,sizeof(uint64_t)*64);
        storage_info storage[64]; memset(storage,0,sizeof(storage_info)*64);
        int count_party=0;

        for(int i=0;i<64;i++){
            std::chrono::steady_clock::time_point begin = std::chrono::steady_clock::now();
            uint64_t new_m=this->parties[i].add(out_key,parties,operand);
            std::chrono::steady_clock::time_point end = std::chrono::steady_clock::now();
            if(new_m!=0){
                if (deactivate==1){
                    counter+=std::chrono::duration_cast<std::chrono::microseconds>(end - begin).count();
                    deactivate=0;
                }
                m_temp[i]=new_m;
                result^=new_m;
                count_party++;
            };
        }
        deactivate=1;

        for(int i=0;i<64;i++){
            if (m_temp[i]!=0){
                std::chrono::steady_clock::time_point begin = std::chrono::steady_clock::now();
                storage[i].location=this->parties[i].store(result^verify_key,result,m_temp[i],&storage[i].table,&storage[i].location); 
                std::chrono::steady_clock::time_point end = std::chrono::steady_clock::now();  
                if (deactivate==1){
                    counter+=std::chrono::duration_cast<std::chrono::microseconds>(end - begin).count();
                    deactivate=0;
                }           
                if(storage[i].location==-1){
                    this->revert(storage);
                    return -1;
                }
            }
        }
        deactivate=1;
        out_key=result^verify_key;
        return 1;
    }

    int store_sequence(uint64_t buffer[], int length){
        //changes the buffer and return the seed
        int seed=rand();
        srand(seed);
        for(int i=0;i<length;i++){
            uint64_t bitmap=(uint64_t)rand()<<32|rand();
            buffer[i]=store_no_change(bitmap,buffer[i]);
        }
        return seed;
    }

    void retrieve_seq(uint64_t buffer[],int seed, int length){
        srand(seed);
        for(int i=0;i<length;i++){
            uint64_t bitmap=(uint64_t)rand()<<32|rand();
            buffer[i]=retrieve(bitmap,buffer[i]);
        }
    }

    ~dv_hash(){
        delete ph;
        delete[] this->parties;
    }
};















//hash to equal parties 
uint64_t gen_rand_test_group(){
    uint64_t x=(uint64_t)rand()<<32|rand();
    return x;
}

void storage_test(){
    ofstream storage_file;
    storage_file.open ("cuckoo_storage_reg.csv");
    storage_file << "inputsize,time [µs]\n";
    int pt_idx[64]; memset(pt_idx,0,64*sizeof(int));
    uint64_t res[2]; memset(res,0,2*sizeof(uint64_t));
    for(int loop=0;loop<13;loop++){
        dv_hash hash_t(64);
        for(int i=0;i<(2<<loop);i++){
            uint64_t group=gen_rand_test_group();
            uint32_t val= rand();
            hash_t.store(group,val,res);
        }
        storage_file << (2<<loop)<<","<<memory_counter<<endl;
        memory_counter=0;
    }
    storage_file.close();
}

void seq_test(){
    //ofstream storage_file;
    ofstream retrieve_file;
    // storage_file.open ("cuckoo_seq_stroage.csv");
    // storage_file << "inputsize,time [µs]\n";
    retrieve_file.open ("cuckoo_seq_retrieval.csv");
    retrieve_file << "inputsize,time [µs]\n";
    //testing sequence stroage ok, do time 
    uint64_t buffer[8192];
    for(int loop=0;loop<12;loop++){ //4 - 2048
        dv_hash hash_t(64);
        for(int i=0;i<(2<<loop);i++){buffer[i]=rand();}
        int seed=hash_t.store_sequence(buffer,(2<<loop));
        // storage_file << (2<<loop)<<","<<counter<<endl;
        // counter=0;
        hash_t.retrieve_seq(buffer,seed,(2<<loop));
        retrieve_file << (2<<loop)<<","<<counter<<endl;
        counter=0;
    }
    //storage_file.close();
    retrieve_file.close();
}

void retrieve_test(){
    dv_hash hash_t(64);
    int group_num;
    int pt_idx[64]; memset(pt_idx,0,64*sizeof(int));
    uint64_t res[2]; memset(res,0,2*sizeof(uint64_t));
    receipt cache[8192];
    
    for(int i=0;i<8192;i++){
        uint64_t group=gen_rand_test_group();
        uint32_t val= rand();
        //cout<<val<<endl;
        if(hash_t.store(group,val,res)==1){
            cache[i].bitmap=res[0];
            cache[i].outkey=res[1];
        }
    }
    counter=0;
    ofstream storage_file;
    storage_file.open ("cuckoo_hash_retrieval.csv");
    storage_file << "inputsize,time [µs]\n";

    for(int loop=0;loop<13;loop++){
        for(int i=0;i<(2<<loop);i++){
            hash_t.retrieve(cache[i].bitmap,cache[i].outkey);
        }
        storage_file << (2<<loop)<<","<<counter<<endl;
        counter=0;
    }
    storage_file.close();
}

void add_test(int n){
    dv_hash hash_t(64);
    int group_num;
    int pt_idx[64]; memset(pt_idx,0,64*sizeof(int));
    uint64_t res[2]; memset(res,0,2*sizeof(uint64_t));
    receipt cache[4096];

    for(int i=0;i<4096;i++){
        uint64_t group=gen_rand_test_group();
        uint32_t val= rand();
        if(hash_t.store(group,val,res)==1){
            cache[i].bitmap=res[0];
            cache[i].outkey=res[1];
        }
    }
    counter=0;
    ofstream storage_file;
    storage_file.open ("cuckoo_hash_FHE_ADD.csv");
    storage_file << "inputsize,time [µs]\n";
    
    for(int loop=0;loop<12;loop++){
        for(int i=0;i<(2<<loop);i++){
            hash_t.add(cache[i].bitmap,cache[i].outkey,n);
        }
        storage_file << (2<<loop)<<","<<counter<<endl;
        counter=0;
    }
    storage_file.close();
}



int main(){
    storage_test();
    //retrieve_test();
    //add_test(4); //fix this
    //seq_test();
    return 0;
}
