"""Enumerate partitions and check Beck's identity with both shifts."""


def partitions(total, ceiling):
    """Yield every partition as a tuple of parts in decreasing order."""
    if total == 0:
        yield ()
        return
    for part in range(min(total, ceiling), 0, -1):
        for remainder in partitions(total - part, part):
            yield (part,) + remainder


def least_three(total):
    return {p for p in partitions(total, total) if p and p[-1] == 3}


def balanced(total):
    return {p for p in partitions(total, total) if 2 * p.count(1) == len(p)}


def main():
    prefix = [0, 0, 0, 1, 0, 0, 1, 1, 1, 2, 2, 3, 4, 5, 6, 9, 10, 13, 17, 21, 25]
    assert [len(least_three(n)) for n in range(len(prefix))] == prefix
    assert least_three(6) == {(3, 3)} and balanced(2) == set()
    print("A026796: a(6) = 1 and b(2) = 0, disproving the stated shift.")

    for n in range(37):
        domain = balanced(n)
        target = least_three(n + 3)
        image = {tuple(part + 1 for part in p if part != 1) + (3,) for p in domain}
        assert len(image) == len(domain) and image == target, n
    print("A026796: exact counts and corrected bijection agree at all 37 tested indices.")


if __name__ == "__main__":
    main()
