#ifndef SIMPLE_HASH
#define SIMPLE_HASH
#include <cstdint>
#ifdef __MSC_VER
#include <intrin.h>
#else
#include <x86intrin.h>  // Not just <immintrin.h> for compilers other than icc
#endif

#include "BOB_hash.h"

template<uint32_t len, uint32_t seed>
unsigned simple_hash(uint32_t key)
{
    unsigned int ret = 0;
    const unsigned char * str = (const unsigned char *)&key;

    for (int i = 0; i < len; i++) {
        ret = ret * seed + str[i];
    }

    return ret;
}

uint32_t (*simple0)(uint32_t) = simple_hash<4, 3>;
uint32_t (*simple1)(uint32_t) = simple_hash<4, 7>;
uint32_t (*simple2)(uint32_t) = simple_hash<4, 11>;
uint32_t (*simple3)(uint32_t) = simple_hash<4, 1007>;
uint32_t (*simple4)(uint32_t) = simple_hash<4, 10007>;
uint32_t (*simple5)(uint32_t) = simple_hash<4, 12263>;
uint32_t (*simple6)(uint32_t) = simple_hash<4, 13613>;
uint32_t (*simple7)(uint32_t) = simple_hash<4, 13093>;
uint32_t (*simple8)(uint32_t) = simple_hash<4, 18007>;


template <uint32_t a>
inline uint32_t multiplicative_hash(uint32_t key)
{
    return __rord((key * a), 7);
}

uint32_t (*multiplicative0)(uint32_t) = multiplicative_hash<2654435761u>;
uint32_t (*multiplicative1)(uint32_t) = multiplicative_hash<0x7fb9b1ef>;
uint32_t (*multiplicative2)(uint32_t) = multiplicative_hash<0xab35dd63>;
uint32_t (*multiplicative3)(uint32_t) = multiplicative_hash<0x41ed960d>;
uint32_t (*multiplicative4)(uint32_t) = multiplicative_hash<0xc7d0125f>;
uint32_t (*multiplicative5)(uint32_t) = multiplicative_hash<0x071f9f8f>;
uint32_t (*multiplicative6)(uint32_t) = multiplicative_hash<0x55ab55b9>;
uint32_t (*multiplicative7)(uint32_t) = multiplicative_hash<0x479ab41d>;
uint32_t (*multiplicative8)(uint32_t) = multiplicative_hash<0x9942f0a5>;

uint32_t (*const hash_func[])(uint32_t) = {
//    BOB1, BOB2, BOB3, BOB4, BOB5, BOB6, BOB7, BOB8,
//    simple1, simple2, simple3, simple4, simple5, simple6, simple7, simple8,
        multiplicative1, multiplicative2, multiplicative3, multiplicative4, multiplicative5, multiplicative6, multiplicative7, multiplicative8,
};

#endif