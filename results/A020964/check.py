from math import isqrt


def floor_sum_values(limit: int) -> list[int]:
    """Compute the floor sum through limit using powers in Z[sqrt(2)]."""
    values = [1]
    c, d = 1, 0
    for _ in range(limit):
        floor_term = 3 * c + isqrt(18 * d * d)
        values.append(values[-1] + floor_term)
        c, d = c + 2 * d, c + d
    return values


def main() -> None:
    limit = 1000
    values = floor_sum_values(limit)
    published_prefix = [1, 4, 11, 28, 70, 171, 417, 1010, 2444, 5905, 14263, 34440]
    assert values[: len(published_prefix)] == published_prefix

    for n in range(7, limit + 1):
        assert values[n] == 3 * values[n - 1] - 4 * values[n - 3] + values[n - 4] + values[n - 5], n

    denominator = [1, -3, 0, 4, -1, -1]
    numerator = [1, 1, -1, -1, 1, 0, 1]
    for n in range(limit + 1):
        coefficient = sum(d * values[n - k] for k, d in enumerate(denominator) if k <= n)
        assert coefficient == (numerator[n] if n < len(numerator) else 0), n

    print(f"A020964: {limit - 6} recurrence checks and {limit + 1} coefficient checks passed.")


if __name__ == "__main__":
    main()
