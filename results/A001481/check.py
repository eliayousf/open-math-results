"""Enumerate sum-of-two-squares pairs at powers of two, using exact integers."""

from bisect import bisect_right
from math import isqrt


def sums_of_two_squares(limit: int) -> set[int]:
    squares = [n * n for n in range(isqrt(limit) + 1)]
    return {
        left + right
        for index, left in enumerate(squares)
        for right in squares[index:bisect_right(squares, limit - left)]
    }


def main() -> None:
    largest_exponent = 20
    represented = sums_of_two_squares(2**largest_exponent)
    pairs_checked = 0
    for exponent in range(largest_exponent + 1):
        total = 2**exponent
        pairs = {
            (left, total - left)
            for left in range(total // 2 + 1)
            if left in represented and total - left in represented
        }
        expected = {(0, total)}
        if exponent > 0:
            expected.add((total // 2, total // 2))
        if pairs != expected:
            raise ValueError(f"2^{exponent} has pairs {sorted(pairs)}, expected {sorted(expected)}")
        pairs_checked += len(pairs)
    print(f"A001481: checked all {pairs_checked} represented pairs through 2^{largest_exponent}.")


if __name__ == "__main__":
    main()
