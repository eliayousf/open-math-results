"""Verify the A001566 witnesses using exact Lucas numbers and modular iteration."""


def fibonacci_pair(index, modulus=None):
    """Return (F(index), F(index + 1)), optionally modulo an integer."""
    if index == 0:
        return 0, 1
    first, second = fibonacci_pair(index // 2, modulus)
    even = first * (2 * second - first)
    odd = first * first + second * second
    low, high = (odd, even + odd) if index % 2 else (even, odd)
    if modulus is not None:
        return low % modulus, high % modulus
    return low, high


def term(index, modulus=None):
    first, second = fibonacci_pair(2 ** (index + 1), modulus)
    value = 2 * second - first
    return value if modulus is None else value % modulus


def verify():
    listed = [3, 7, 47, 2207, 4870847]
    if [term(index) for index in range(len(listed))] != listed:
        raise ValueError("Lucas computation does not match the OEIS terms")

    for index, scale, p in [(3, 8, 5), (10, 40, 19)]:
        quotient, remainder = divmod(term(index) - 7, scale)
        if remainder or quotient <= 0 or quotient % (p * p):
            raise ValueError(f"Invalid counterexample at index {index}")
        print(f"A001566: index {index}, denominator {scale}, square divisor {p * p}")

    modulus = 40 * 19**2
    orbit = [3]
    for _ in range(10):
        orbit.append((orbit[-1] ** 2 - 2) % modulus)
    if orbit != [term(index, modulus) for index in range(11)] or orbit[-1] != orbit[1]:
        raise ValueError(f"Incorrect residue cycle: {orbit}")
    for index in [19, 28, 37, 46]:
        if term(index, modulus) != 7:
            raise ValueError(f"Invalid repeated residue at index {index}")


if __name__ == "__main__":
    verify()
