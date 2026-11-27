"""Check Tisdale's identity by direct integer enumeration."""

from math import isqrt


def is_prime(n):
    return n >= 2 and all(n % divisor for divisor in range(2, isqrt(n) + 1))


def check(limit=3000):
    primes = [n for n in range(2, limit + 1) if is_prime(n)]
    quadratic_values = {k * k + k + 1 for k in range(isqrt(limit) + 1)}

    a007645 = [prime for prime in primes if prime % 3 in (0, 1)]
    a002383 = [prime for prime in primes if prime in quadratic_values]
    quadratic_divisors = [
        prime
        for prime in primes
        if any((k * k + k + 1) % prime == 0 for k in range(prime))
    ]
    a162471 = [prime for prime in quadratic_divisors if prime not in quadratic_values]

    assert a007645[:8] == [3, 7, 13, 19, 31, 37, 43, 61]
    assert a002383[:8] == [3, 7, 13, 31, 43, 73, 157, 211]
    assert a162471[:8] == [19, 37, 61, 67, 79, 97, 103, 109]
    assert sorted(set(a002383) | set(a162471)) == a007645
    print(f"A007645: verified union by integer enumeration for {len(primes)} primes through {limit}.")


if __name__ == "__main__":
    check()
