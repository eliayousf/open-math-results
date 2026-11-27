#!/usr/bin/env python3
"""Count all partitions into threes and fives through a fixed bound."""


def partition_counts(limit: int) -> list[int]:
    counts = [0] * (limit + 1)
    for threes in range(limit // 3 + 1):
        for total in range(3 * threes, limit + 1, 5):
            counts[total] += 1
    return counts


def main() -> None:
    limit = 5000
    counts = partition_counts(limit)

    assert counts[:15] == [1, 0, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1]
    for n, count in enumerate(counts):
        layman = 2 * (n + 3) // 3 - 3 * (n + 3) // 5
        akinari = (2 * n + 5) // 5 - (n + 2) // 3
        assert count == layman == akinari, (n, count, layman, akinari)

    print(f"A008676: exact enumeration agrees with both formulas through n={limit}.")


if __name__ == "__main__":
    main()
