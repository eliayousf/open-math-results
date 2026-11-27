"""Verify Shunia's A002457 identity with integer and rational arithmetic."""

from fractions import Fraction
from math import factorial, isqrt


def check(n):
    base = 16**n
    radicand = (base + 1) ** (2 * n + 1)
    root = isqrt(radicand)
    expected = factorial(2 * n + 1) // factorial(n) ** 2
    if root % base != expected:
        raise ValueError(f"The square-root remainder differs from the factorial formula at n={n}")

    coefficient = Fraction(4**n)
    truncation = 0
    for j in range(n + 1):
        if coefficient.denominator != 1:
            raise ValueError(f"The coefficient at n={n}, j={j} is fractional")
        truncation = truncation * base + coefficient.numerator
        coefficient *= Fraction(2 * n + 1 - 2 * j, 2 * (j + 1))

    if not 0 < coefficient / base < 1 or truncation != root:
        raise ValueError(f"The truncation bound or reconstructed square root fails at n={n}")


def main():
    indices = [*range(1, 121), 150, 200, 256]
    for n in indices:
        check(n)
    print(f"A002457: exact checks passed at {len(indices)} indices, through n={max(indices)}.")


if __name__ == "__main__":
    main()
