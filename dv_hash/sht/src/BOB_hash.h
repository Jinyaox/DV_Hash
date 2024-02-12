#ifndef COLORINGCLASSIFER_BOB_HASH_H
#define COLORINGCLASSIFER_BOB_HASH_H

#include <cstdlib>
#include <cstdint>

#define mix(a,b,c) \
{ \
  a -= b; a -= c; a ^= (c>>13); \
  b -= c; b -= a; b ^= (a<<8); \
  c -= a; c -= b; c ^= (b>>13); \
  a -= b; a -= c; a ^= (c>>12);  \
  b -= c; b -= a; b ^= (a<<16); \
  c -= a; c -= b; c ^= (b>>5); \
  a -= b; a -= c; a ^= (c>>3);  \
  b -= c; b -= a; b ^= (a<<10); \
  c -= a; c -= b; c ^= (b>>15); \
}

template<size_t len, uint32_t seed>
uint32_t BOB(uint32_t key)
{
    const char * str = (const char *)&key;
    //register ub4 a,b,c,len;
    unsigned int a,b,c;
    unsigned int initval = seed;
    /* Set up the internal state */
    //len = length;
    a = b = 0x9e3779b9;  /* the golden ratio; an arbitrary value */
    c = initval;         /* the previous hash value */

    /*---------------------------------------- handle most of the key */
//    while (len >= 12)
//    {
//        a += (str[0] +((unsigned int)str[1]<<8) +((unsigned int)str[2]<<16) +((unsigned int)str[3]<<24));
//        b += (str[4] +((unsigned int)str[5]<<8) +((unsigned int)str[6]<<16) +((unsigned int)str[7]<<24));
//        c += (str[8] +((unsigned int)str[9]<<8) +((unsigned int)str[10]<<16)+((unsigned int)str[11]<<24));
//        mix(a,b,c);
//        str += 12; len -= 12;
//    }

    /*------------------------------------- handle the last 11 bytes */
    c += len;
    switch(len)              /* all the case statements fall through */
    {
    case 11: c+=((unsigned int)str[10]<<24);
    case 10: c+=((unsigned int)str[9]<<16);
    case 9 : c+=((unsigned int)str[8]<<8);
        /* the first byte of c is reserved for the length */
    case 8 : b+=((unsigned int)str[7]<<24);
    case 7 : b+=((unsigned int)str[6]<<16);
    case 6 : b+=((unsigned int)str[5]<<8);
    case 5 : b+=str[4];
    case 4 : a+=((unsigned int)str[3]<<24);
    case 3 : a+=((unsigned int)str[2]<<16);
    case 2 : a+=((unsigned int)str[1]<<8);
    case 1 : a+=str[0];
        /* case 0: nothing left to add */
    }
    mix(a,b,c);
    /*-------------------------------------------- report the result */
    return c;
}

uint32_t (*BOB0)(uint32_t) = BOB<4, 0x03>;
uint32_t (*BOB1)(uint32_t) = BOB<4, 0xDEADBEEF>;
uint32_t (*BOB2)(uint32_t) = BOB<4, 0x13374EA7>;
uint32_t (*BOB3)(uint32_t) = BOB<4, 0x5fc1ec7e>;
uint32_t (*BOB4)(uint32_t) = BOB<4, 0xac59b244>;
uint32_t (*BOB5)(uint32_t) = BOB<4, 0x19b44716>;
uint32_t (*BOB6)(uint32_t) = BOB<4, 0x0A8f4dff>;
uint32_t (*BOB7)(uint32_t) = BOB<4, 0x417c0d80>;
uint32_t (*BOB8)(uint32_t) = BOB<4, 0x801AE677>;

#endif //COLORINGCLASSIFER_BOB_HASH_H
