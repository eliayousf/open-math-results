"""Check Mathar's recurrence using factorial counts and small permutation enumeration."""

from itertools import permutations
from math import factorial


def even_involutions(n, factorials):
    count = 0
    for j in range(n // 4 + 1):
        denominator = 2 ** (2 * j) * factorials[2 * j] * factorials[n - 4 * j]
        term, remainder = divmod(factorials[n], denominator)
        if remainder:
            raise ValueError(f"Nonintegral involution count at n={n}, j={j}")
        count += term
    return count


def brute_force(n):
    count = 0
    for perm in permutations(range(n)):
        if all(perm[perm[i]] == i for i in range(n)):
            moved = sum(perm[i] != i for i in range(n))
            count += moved % 4 == 0
    return count


def main():
    limit = 300
    factorials = [factorial(n) for n in range(limit + 1)]
    values = [even_involutions(n, factorials) for n in range(limit + 1)]
    initial = [1, 1, 1, 1, 4, 16, 46, 106, 316, 1324, 5356, 18316, 63856]
    if values[:len(initial)] != initial:
        raise ValueError("The factorial formula differs from the OEIS prefix")
    for n in range(9):
        if values[n] != brute_force(n):
            raise ValueError(f"The factorial formula differs from direct counting at n={n}")
    for n in range(5, limit + 1):
        difference = values[n] - 3 * values[n - 1] + 3 * values[n - 2] - values[n - 3]
        correction = (n - 1) * (n - 3) * values[n - 4] - (n - 3) * (n - 4) * values[n - 5]
        if difference != correction:
            raise ValueError(f"The recurrence fails at n={n}")
    print(f"A000704: direct counts through n=8 and {limit - 4} recurrence checks passed.")


if __name__ == "__main__":
    main()
