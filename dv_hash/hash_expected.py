import math

def generate_primes(limit):
    primes = []
    is_prime = [True] * (limit + 1)
    is_prime[0] = is_prime[1] = False

    for num in range(2, int(limit**0.5) + 1):
        if is_prime[num]:
            primes.append(num)
            for multiple in range(num * num, limit + 1, num):
                is_prime[multiple] = False

    for num in range(int(limit**0.5) + 1, limit + 1):
        if is_prime[num]:
            primes.append(num)

    return primes

# Generate the first 256 prime numbers
first_256_primes = sum(set(generate_primes(2000)[:128]))

def expected_value(parties,total_sum,number):
    if parties==1:
        return total_sum/number
    else:
        selected=total_sum/number
        return selected*expected_value(parties-1,total_sum-selected,number-1)


def re_hash_probability(number_size,party_size):
    """
    Prime Size/Number Size is P
    Party Size is N
    """
    start=1
    for i in range(1,party_size):
        start*=(number_size-i)/number_size
    return 1-start

"""
Given a particular party size, find a prime range that satisfy low rehash probability and good prime size
"""


for i in range(1,65):
    print(f"for a party of {i}, the expected CRT product to cover is:  {expected_value(i,first_256_primes,256)}")
# for i in range(1,65):
#     print(f"for a party of {i}, the expected Rehash Probability Is:  {re_hash_probability(256,i)}")

print(re_hash_probability(256,5))
