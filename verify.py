"""Verify the finite certificate for the dihedral difference characteristic."""
import json
from itertools import combinations
from math import isqrt
from pathlib import Path

CUTOFF = 1_212_464


def require(condition, message):
    if not condition:
        raise ValueError(message)


def differences(a, b):
    return {x - y for x in a for y in b}


def residues(values, n):
    return {v % n for v in values}


def prime_power(q):
    if q < 2:
        return False
    p = next((i for i in range(2, isqrt(q) + 1) if q % i == 0), q)
    while q % p == 0:
        q //= p
    return q == 1


def template(k):
    if k in (4, 5, 6):
        h = k - 2
        return list(range(h)), [0, -h]
    require(k in (8, 9, 10, 11), "unknown template")
    b = k - 4
    return [0, 1, 2*b-1, 2*b], [-2*j for j in range(b-1)] + [-(2*b-3)]


def width(u, v):
    mono = differences(u, u) | differences(v, v)
    radius = 0
    while radius + 1 in mono:
        radius += 1
    cross = differences(u, v)
    right = 0
    require(0 in cross, "expected cross interval beginning at zero")
    while right + 1 in cross:
        right += 1
    return min(2*radius, right)


def check_direct(n, a, b):
    a, b = residues(a, n), residues(b, n)
    require(11*(len(a) + len(b))**2 <= 64*n, f"size at {n}")
    require(len(residues(differences(a, b), n)) == n, f"reflections at {n}")
    mono = differences(a, a) | differences(b, b)
    require(len(residues(mono, n)) == n, f"rotations at {n}")


def main():
    data = json.loads(Path(__file__).with_name("certificate.json").read_text(encoding="utf-8"))
    covered = bytearray(CUTOFF)
    gaps = {}
    for key, s in data["short_sets"].items():
        q = int(key)
        m = q*q + q + 1
        require(len(set(s)) == q+1 and min(s) == 0 and max(s) < m, key)
        require(len(residues(differences(s, s), m)) == m, key)
        gaps[q] = m-1-max(s)
    for k, q in data["lifts"]:
        require(prime_power(q), f"invalid Singer parameter {q}")
        u, v = template(k)
        size = (len(u) + len(v))*(q+1)
        lo = (11*size**2 + 63)//64
        hi = min(CUTOFF-1, width(u, v)*(q*q+q+1) + 2*gaps.get(q, q) + 1)
        require(1 <= lo <= hi, f"empty lift {k,q}")
        covered[lo:hi+1] = bytes([1])*(hi-lo+1)
    missing = [n for n in range(1, CUTOFF) if not covered[n]]
    print(f"Lifts: {len(data['lifts'])}. Uncovered after lifts: {len(missing)}. Largest: {max(missing)}.")
    for row in data["small"]:
        n = row["n"]
        check_direct(n, row["A"], row["B"])
        covered[n] = 1
    for row in data["direct"]:
        for n in row["n"]:
            check_direct(n, range(row["a"]), row["B"])
            covered[n] = 1
    require(all(covered[1:]), "uncovered parameter")
    print(f"Covered every integer from 1 through {CUTOFF-1:,}.")
    # At most seven elements and |A||B| >= 11 force sizes 3 and 4.
    cross_count = 0
    for a in combinations(range(11), 3):
        for b in combinations(range(11), 4):
            if len(residues(differences(a, b), 11)) == 11:
                cross_count += 1
                mono = differences(a, a) | differences(b, b)
                require(len(residues(mono, 11)) < 11, "seven-element basis found")
    print(f"D22: {cross_count} cross covers among 54,450 pairs; zero seven-element bases.")


if __name__ == "__main__":
    main()
