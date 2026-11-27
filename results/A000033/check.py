"""Compare both A000033 formulas and check a finite grid of congruences."""

from fractions import Fraction
from math import comb, isqrt


def published_formula(n, factorials):
    total = Fraction(0)
    for k in range(2, n + 1):
        numerator = (-1) ** k * n * factorials[2 * n - k - 1] * factorials[n - k]
        denominator = factorials[2 * n - 2 * k] * factorials[k - 2]
        total += Fraction(numerator, denominator)
    if total.denominator != 1:
        raise ValueError(f"The published formula was fractional at n={n}")
    return total.numerator


def lean_formula(n, factorials):
    total = 0
    for r in range(n + 1):
        rook_count = comb(n + r, 2 * r) + comb(n + r - 1, 2 * r)
        total += (-1) ** r * factorials[r] * comb(n - r, 2) * rook_count
    return (-1) ** n * total


def main():
    limit = 600
    factorials = [1]
    for k in range(1, 2 * limit + 1):
        factorials.append(k * factorials[-1])

    values = [0]
    for n in range(1, limit + 1):
        value = published_formula(n, factorials)
        if value != lean_formula(n, factorials):
            raise ValueError(f"The two formulas differ at n={n}")
        values.append(value)

    tabulated = [0, 2, 3, 4, 40, 210, 1477, 11672, 104256, 1036050, 11338855, 135494844]
    if values[1 : 1 + len(tabulated)] != tabulated:
        raise ValueError("The sequence differs from the initial terms published by OEIS")

    primes = [p for p in range(2, 98) if all(p % d for d in range(2, isqrt(p) + 1))]
    for p in primes:
        for n in range(1, 401):
            if (values[n] + 2 * values[n + p] + values[n + 2 * p]) % p:
                raise ValueError(f"The congruence fails at n={n}, p={p}")

    print(f"A000033: {limit} formula comparisons and {400 * len(primes):,} congruence checks passed.")


if __name__ == "__main__":
    main()
