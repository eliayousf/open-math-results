"""Compare the signed formula with the defining enumeration of A006364."""

from itertools import count, islice


def qualifying_integers():
    return (m for m in count() if bin(m // 2).count("1") % 2 == 0)


def signed_formula(n):
    weight = bin(n - 1).count("1")
    return 2 * n + (-1) ** (n - weight) - (3 + (-1) ** n) // 2


def main():
    limit = 100_000
    for index, value in enumerate(islice(qualifying_integers(), limit), start=1):
        formula_value = signed_formula(index)
        if value != formula_value:
            raise ValueError(f"A006364 at n={index}: enumeration {value}, formula {formula_value}")
    print(f"A006364: exact signed formula agrees with the direct enumeration through n={limit:,}.")


if __name__ == "__main__":
    main()
