#include <iostream>
#include <stdlib.h>
#include "crt.h"
#include "xor.h"
#include "helper.h"
#include "../xxHash/xxhash.h"
#include <limits.h>
#include <chrono>
#include <fstream>
using namespace std;

//compile with clang++ dv_hash.cpp ../xxHash/libxxhash.0.8.2.dylib -o dv_hash_test

typedef struct hash_store{
    uint8_t active;
    uint64_t m_sum;
    uint64_t sum_without_i;
}hash_store;

typedef struct receipt{
    uint64_t bitmap;
    uint64_t outkey;
}receipt;

int conflict_ctr=0;
long time_counter=0;
short deactivate=1;


int cmpfunc_min (const void * a, const void * b) {
   return -( *(int*)a - *(int*)b );
}

/*helper functions*/
long find_max(int array[],int table_size, int computation_size){
   qsort(array, table_size, sizeof(int), cmpfunc_min); 

   long product=0;

   for(int i=0;i<computation_size;i++){
    product=product*array[i];
   }
   return product;
}

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
        //check too big? ret 0;
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

class hash_table{
    public: 
    hash_store* hash;
    int t_size;

    int current_value;

    hash_table(unsigned size){
        this->t_size=size;
        hash= new hash_store[size];
        memset(hash,0,sizeof(hash_store)*size);
    }

    int can_store(XXH64_hash_t seed, uint64_t value,uint64_t sum_m,uint64_t mi){
        short ret_val;
        long position=(uint64_t)XXH64(&value,8,seed) % t_size;
        long incre=1;
        while(hash[position].active!=0){
            if((hash[position].m_sum==sum_m)&&(hash[position].sum_without_i^hash[position].m_sum^(uint64_t)seed==mi)){
                return position;
            }
            position=(position+(incre*incre))%t_size;
            incre++;
            if(incre>128){
                return -1;
            }
        }
        return position;
    }

    short store(int position, uint64_t value, uint64_t m_sum, uint64_t m_withou_i){
        hash[position].m_sum=m_sum;
        hash[position].sum_without_i=m_withou_i;
        hash[position].active=1;
        return 1;
    }

    short retrieve(uint64_t out_key, int prime_remainder_pair[], uint64_t verifier, XXH64_hash_t seed, uint64_t mask){

        long loc=(uint64_t)XXH64(&out_key,8,seed) % t_size;
        uint64_t m_sum=hash[loc].m_sum^(uint64_t)seed^mask;
        unsigned incre=1;

        while((out_key^m_sum)!=verifier){
            loc=(loc+(incre*incre))%t_size;
            incre++;
            m_sum=hash[loc].m_sum^(uint64_t)seed^mask;
            if(incre>128){
                return 0; //not expected to return 0;
            }
        }
        uint64_t final_answer=m_sum^(hash[loc].sum_without_i);
        final_answer=final_answer ^ mask;
        prime_remainder_pair[0]=final_answer>>32;
        prime_remainder_pair[1]=final_answer & 0x00000000FFFFFFFF;
        return 1;
    }

    ~hash_table(){
        delete[] hash;
    }
};

class node{
    public:
    uint64_t index_key; //the mask thing for m1 m2 m3 hash (a mask)
    short ID;
    int place;
    int prime_size;
    int key_size; //the degree of the polynomial 
    hash_table* table;
    XXH64_hash_t seed;

    node(){
        seed =(XXH64_hash_t) rand();
    }

    void init(int table_size, int p_size, short id, uint64_t index_key){
        this->ID=id;
        this->index_key=index_key;
        table=new hash_table(table_size);
        prime_size=p_size;
    }

    int eval(int val,int max_prime){
        return (int)((uint64_t) XXH64(&val,4,seed) % max_prime);
    }

    int can_store(uint64_t out_key,uint64_t sum_m,uint64_t mi){
        this->place=table->can_store(seed,out_key,sum_m^(uint64_t)seed^index_key,mi);
        return this->place;
    }

    short store(int loc,uint64_t out_key, uint64_t sum_m, uint64_t m){
        return table->store(loc,out_key,sum_m^(uint64_t)seed^index_key,sum_m^m);
    }

    short retrieve(uint64_t out_key, uint64_t index, int prime_remainder_pair[], uint64_t k_sum){
        //store the result in prime remainder pair if valid, else return 0

        uint64_t mask=((uint64_t)1)<<this->ID;
        if((index&mask)==0){return 0;} //not your turn
        return this->table->retrieve(out_key,prime_remainder_pair,k_sum,seed,this->index_key);
    }

    //finish the retrieve function requires k_sum, m_sum, 

    uint64_t gen_m(prime_hashes* ph, int idx, uint64_t val){
        uint64_t prime=ph->primes[idx];
        uint64_t remainder=val%prime;
        uint64_t piri=(prime<<32|remainder);
        uint64_t res=piri ^ index_key;
        return res;
    }

    ~node(){
        delete table;
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


    short store(int party_index[],int party_size,uint64_t val, uint64_t result[2]){
        int hash_index[64];
        int collision[64];

        memset(collision,-1,party_size*sizeof(int));
        memset(hash_index,-1,party_size*sizeof(int));
        ph->clear_lock();
        node* current;
        int id;
        std::chrono::steady_clock::time_point begin = std::chrono::steady_clock::now();
        for(int i=0;i<party_size;i++){
            current=&(this->parties[party_index[i]]);
            id=current->eval(val,256);
            int debug=ph->lock[id];
            if(ph->lock[id]!=1){
                hash_index[i]=id;
                ph->lock[id]=1;
            }
            else{
                collision[i]=id;
            }
        }

        int place=0; //the iterator for the normal parties (use this first)
        int collision_substitute=0; //iterator for substituting party
        int current_idx;
        int debug=0;
        int revert=0; //make sure clear it

        while(ph->can_gen(hash_index,val,party_size)==0){ //see if the current hash indexes are sufficiently large

            if(place>=party_size){ //exhausted all the possible existing parties
                debug = collision[collision_substitute];

                while(debug==-1){ //find the next 

                    //the if condition checks if we used all possible values
                    if(collision_substitute>=party_size){
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
                    if(place>=party_size){
                        break;
                    }
                    else{
                        place++;
                    }
                }
            }
        }
        std::chrono::steady_clock::time_point end = std::chrono::steady_clock::now();
        time_counter+=std::chrono::duration_cast<std::chrono::microseconds>(end - begin).count();

        uint64_t all_m [64];
        int final_party[64];

        memset(all_m,0,sizeof(uint64_t)*party_size);

        for(int i=0;i<party_size;i++){
            current_idx=hash_index[i];
            if(current_idx!=-1){
                current=&this->parties[party_index[i]];//get the party associated with it
                final_party[i]=party_index[i]; //get the final party size and nodes;
                begin = std::chrono::steady_clock::now();
                all_m[i]=current->gen_m(ph,current_idx,val);
                end = std::chrono::steady_clock::now();
                if(deactivate==1){
                    time_counter+=std::chrono::duration_cast<std::chrono::microseconds>(end - begin).count();
                    deactivate=0;
                }
            }
        }
        deactivate=1;

        begin = std::chrono::steady_clock::now();
        uint64_t sum_m=gen_sum_m(all_m,party_size);
        end = std::chrono::steady_clock::now();
        time_counter+=std::chrono::duration_cast<std::chrono::microseconds>(end - begin).count();
        
        //check if individual hash table has issues 
        begin = std::chrono::steady_clock::now();
        for(int i=0;i<party_size;i++){
            current_idx=hash_index[i];
            if(current_idx!=-1){
                current=&this->parties[party_index[i]]; //get the party associated with it                
                if(current->can_store(sum_m^verify_key,sum_m,all_m[i])==-1){
                    return 0;
                };
            }
        }
        end = std::chrono::steady_clock::now();
        time_counter+=std::chrono::duration_cast<std::chrono::microseconds>(end - begin).count();

        //now we finally store something
        for(int i=0;i<party_size;i++){
            current_idx=hash_index[i];
            if(current_idx!=-1){
                current=&this->parties[party_index[i]]; //get the party associated with it
                current->store(current->place,sum_m^verify_key,sum_m,all_m[i]);
            }
        }

        begin = std::chrono::steady_clock::now();
        result[0]= gen_party_indexes(final_party,party_size); 
        result[1]= sum_m ^ verify_key;
        end = std::chrono::steady_clock::now();
        time_counter+=std::chrono::duration_cast<std::chrono::microseconds>(end - begin).count();

        return 1;
    }

    uint64_t retrieve(uint64_t parties, uint64_t out_key){
        int value_storage[]={0,0};
        uint64_t primes[64],remainder[64];
        int counter=0; uint64_t lcm=1; uint64_t OLD_lcm=1; //prevent LCM overflow
        for(int i=0;i<64;i++){
            std::chrono::steady_clock::time_point begin = std::chrono::steady_clock::now();
            if(this->parties[i].retrieve(out_key,parties,value_storage,verify_key)==1){
                remainder[counter]=value_storage[1]; 
                primes[counter]=value_storage[0]; 
                counter++;
            };
            std::chrono::steady_clock::time_point end = std::chrono::steady_clock::now();
            if((deactivate==1)&&(counter!=0)){
                time_counter+=std::chrono::duration_cast<std::chrono::microseconds>(end - begin).count();
                deactivate=0;
            }
        }
        std::chrono::steady_clock::time_point begin = std::chrono::steady_clock::now();
        uint64_t result=CRT(primes,remainder,counter);
        std::chrono::steady_clock::time_point end = std::chrono::steady_clock::now();
        time_counter+=std::chrono::duration_cast<std::chrono::microseconds>(end - begin).count();
        deactivate=1;
        return result;
    }

    ~dv_hash(){
        delete ph;
        delete[] this->parties;
    }
};















//testing scripts
int gen_rand_test_group(int array[]){
    uint32_t x=(rand()^rand());
    int counter=0;;
    for(int i=0;i<32;i++){
        if((x & 1<<i) != 0){
            array[counter]=i;
            counter++;
        }
    }
    return counter;
}

void storage_test(){
    ofstream storage_file;
    storage_file.open ("naive_hash_stroage.csv");
    storage_file << "inputsize,time [µs]\n";

    for(int loop=1;loop<13;loop++){ //4 - 2048
        dv_hash hash_t(64);
        int group_num;
        int pt_idx[64]; memset(pt_idx,0,64*sizeof(int));
        uint64_t res[2]; memset(res,0,2*sizeof(uint64_t));

        for(int i=0;i<(2<<loop);i++){
            group_num=gen_rand_test_group(pt_idx);
            uint32_t val= rand();
            hash_t.store(pt_idx,group_num,val,res);
        }
        storage_file << (2<<loop)<<","<<time_counter<<endl;
        time_counter=0;
    }
    storage_file.close();
}

void retrieve_test(){
    dv_hash hash_t(64);
    int group_num;
    int pt_idx[64]; memset(pt_idx,0,64*sizeof(int));
    uint64_t res[2]; memset(res,0,2*sizeof(uint64_t));
    receipt cache[8192];
    
    for(int i=0;i<8192;i++){
        group_num=gen_rand_test_group(pt_idx);
        uint32_t val= rand();
        hash_t.store(pt_idx,group_num,val,res);
        cache[i].bitmap=res[0];
        cache[i].outkey=res[1];
    }
    time_counter=0;
    ofstream storage_file;
    storage_file.open ("naive_hash_retrieval.csv");
    storage_file << "inputsize,time [µs]\n";

    for(int loop=1;loop<13;loop++){
        for(int i=0;i<(2<<loop);i++){
            hash_t.retrieve(cache[i].bitmap,cache[i].outkey);
        }
        storage_file << (2<<loop)<<","<<time_counter<<endl;
        time_counter=0;
    }
    storage_file.close();
}

int main(){
    //storage_test();
    retrieve_test();
    return 0;
}
