"""Generate the two source sequences by exact finite convolution."""

from math import comb


def convolve(left, right):
    return [sum(left[j] * right[n - j] for j in range(n + 1)) for n in range(len(left))]


def verify():
    limit = 300
    geometric_two = [2**n for n in range(limit + 1)]
    alternating_even = [0 if n % 2 else (-1) ** (n // 2) for n in range(limit + 1)]
    common = convolve(geometric_two, alternating_even)

    # For (1-x-2*x^3)^(-1), choose j cubic factors among n-2*j factors.
    cubic_reciprocal = [
        sum(2**j * comb(n - 2 * j, j) for j in range(n // 3 + 1))
        for n in range(limit + 1)
    ]
    a = convolve(common, cubic_reciprocal)
    b = convolve(common, [1] * (limit + 1))

    if a[:9] != [1, 3, 6, 14, 33, 71, 150, 318, 665]:
        raise AssertionError("A003477 initial terms do not match OEIS")
    if b[:9] != [1, 3, 6, 12, 25, 51, 102, 204, 409]:
        raise AssertionError("A077854 initial terms do not match OEIS")
    if a[4] != 33 or b[4] + 2 * a[1] != 31:
        raise AssertionError("The stated index-four counterexample did not reproduce")

    for n in range(3, limit + 1):
        corrected = b[n] + 2 * sum(a[: n - 2])
        printed = b[n] + 2 * sum(a[1 : n - 2])
        if a[n] != corrected or a[n] - printed != 2:
            raise AssertionError(f"Unexpected discrepancy at n={n}")

    print(f"A003477: counterexample 33 ≠ 31 and {limit - 2} corrected equalities verified.")


if __name__ == "__main__":
    verify()
