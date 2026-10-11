"""verify33.py -- verify the MECHANISM of 33-complete-proof.md.

For several a1: build the sequence (window B), let P = primes <= a1^2,
F = {S(a_n)} with S(a) = {p in P : p | a}. Then check:
  (L1) for all a in [a1,B]:  a is a term  <=>  S(a) in F        (Lemma 4.1)
  (C2) every preceq-minimal term has all prime factors <= a1^2  (Corollary 3.2)
Usage: python verify33.py [B]
"""
import sys
from math import gcd

def spf_sieve(n):
    spf = list(range(n + 1))
    i = 2
    while i * i <= n:
        if spf[i] == i:
            for j in range(i * i, n + 1, i):
                if spf[j] == j:
                    spf[j] = i
        i += 1
    return spf

def _supp(x, spf):
    out = []
    while x > 1:
        p = spf[x]
        out.append(p)
        while x % p == 0:
            x //= p
    return out

def build(a1, B, spf):
    """terms <= B; alive[y] iff y shares a prime with EVERY earlier term."""
    alive = bytearray([1]) * (B + 1)
    alive[0] = alive[1] = 0
    for j in range(2, a1):
        alive[j] = 0
    terms = []
    cur = a1
    while True:
        k = cur + 1
        while k <= B and not alive[k]:
            k += 1
        if k > B:
            break
        terms.append(k)
        for y in range(k + 1, B + 1):
            if alive[y] and gcd(y, k) == 1:
                alive[y] = 0
        cur = k
    return terms

def main():
    B = int(sys.argv[1]) if len(sys.argv) > 1 else 4000
    spf = spf_sieve(B + 1)
    cases = [2, 3, 4, 6, 12, 15, 30, 35, 45, 99, 121, 175, 187, 899]
    allok = True
    for a1 in cases:
        if a1 > B // 2:
            continue
        terms = set(build(a1, B, spf))
        F = set()
        for t in terms:
            F.add(frozenset(p for p in _supp(t, spf) if p <= a1 * a1))
        bad = []
        for a in range(a1, B + 1):
            S = frozenset(p for p in _supp(a, spf) if p <= a1 * a1)
            if (a in terms) != (S in F):
                bad.append((a, a in terms, sorted(S), S in F))
        badmin = []
        ts = sorted(terms)
        rads = {t: set(_supp(t, spf)) for t in ts}
        for t in ts:
            ismin = True
            for s in ts:
                if s < t and rads[s] <= rads[t]:
                    ismin = False
                    break
            if ismin:
                big = [p for p in rads[t] if p > a1 * a1]
                if big:
                    badmin.append((t, big))
        ok = (not bad) and (not badmin)
        allok &= ok
        print("a1=%-4d terms=%-5d |F|=%-4d  L1viol=%d C2viol=%d  %s"
              % (a1, len(terms), len(F), len(bad), len(badmin), "OK" if ok else "FAIL"))
        if bad[:3]:
            print("     L1 e.g.:", bad[:3])
        if badmin[:3]:
            print("     C2 e.g.:", badmin[:3])
    print("ALL:", "OK" if allok else "FAIL")

main()
