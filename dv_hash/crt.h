#ifndef __CRT__
#define __CRT__
#include <stdlib.h>
#include <iostream>
using namespace std;

uint64_t inv(uint64_t a, uint64_t m) 
{ 
    long m0 = m, t, q; 
    long x0 = 0, x1 = 1; //0
  
    if (m == 1) 
        return 0; 
  
    // Apply extended Euclid Algorithm 
    while (a > 1) { 
        if(m==0){
            return 1; //stub
        }
        // q is quotient now we have a division by 0 error
        q = a / m; 
  
        t = m; 
  
        // m is remainder now, process same as 
        // euclid's algo 
        m = a % m, a = t; 
  
        t = x0; 
  
        x0 = x1 - q * x0; 
  
        x1 = t; 
    } 
  
    // Make x1 positive 
    if (x1 < 0) 
        x1 += m0; 
  
    return x1; 
}

uint64_t CRT(uint64_t num[], uint64_t rem[], uint64_t k) 
{ 
    // Compute product of all numbers 
    uint64_t prod = 1; 
    uint64_t old_prod=prod;
    int counter=0;
    for (int i = 0; i < k; i++){
        old_prod=prod;
        prod *= num[i]; 
        if(prod>4294967295){ //max of 32 bit int
            counter++;
            break;
        }
        counter++;
    }
  
    // Initialize result 
    uint64_t result = 0; 
  
    // Apply above formula 
    for (uint64_t i = 0; i < counter; i++) { 
        uint64_t pp = prod / num[i]; 
        uint64_t tempr=rem[i];
        uint64_t inverse=inv(pp, num[i]);
        tempr*=pp;
        tempr*=inverse;
        result += tempr; 
    } 
  
    return result % prod; 
}

#endif