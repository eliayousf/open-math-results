"""Check A005994 and A203286 independently with exact counts."""

from collections import Counter
from itertools import combinations, combinations_with_replacement
from math import comb


def pairs_at_total(total):
    """Group multiplicity triples by weighted sum without using their differences."""
    weights = Counter(
        one + 2 * two + 3 * (total - one - two)
        for one in range(total + 1)
        for two in range(total - one + 1)
    )
    return sum(size**2 for size in weights.values())


def array_count_direct(n):
    return sum(
        sum(array) == 0 and sum(x < 0 for x in array) == sum(x > 0 for x in array)
        for array in combinations_with_replacement(range(-3, 4), 2 * n)
    )


def alkane_count(n):
    """Fix the unique blue bead and use Burnside's lemma for reflection."""
    slots = n + 4
    # A fixed red subset uses two of the reflected pairs. The center is black
    # when it exists, because the red count is even.
    return (comb(slots, 4) + comb(slots // 2, 2)) // 2


def alkane_count_direct(n):
    slots = n + 4
    return len(
        {
            min(red, tuple(slots - 1 - j for j in reversed(red)))
            for red in combinations(range(slots), 4)
        }
    )


def alkane_convolution(n):
    return sum((2 * d + 1) * comb(n - 2 * d + 2, 2) for d in range(n // 2 + 1))


def main():
    for n in range(6):
        assert sum(pairs_at_total(j) for j in range(n + 1)) == array_count_direct(n), n
    for n in range(13):
        assert alkane_count(n) == alkane_count_direct(n), n

    assert [alkane_count(n) for n in range(7)] == [1, 3, 9, 19, 38, 66, 110]
    assert [array_count_direct(n) for n in range(1, 6)] == [4, 12, 28, 57, 104]

    # Reuse the cumulative counts for each size instead of recalculating
    # all smaller multiplicity totals at every index.
    running = 0
    for n in range(201):
        running += pairs_at_total(n)
        assert alkane_count(n) == alkane_convolution(n), n
        if n:
            assert alkane_count(n - 1) + alkane_count(n) == running, n

    print("A005994: direct counts and 200 exact adjacent-sum checks passed.")


if __name__ == "__main__":
    main()
