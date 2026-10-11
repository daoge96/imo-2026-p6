#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""长程检查：a1=15015 的 F_n 是否最终稳定；并观察极大集大小演化。"""
from collections import defaultdict


def supp(n):
    s = set()
    if n % 2 == 0:
        s.add(2)
        while n % 2 == 0:
            n //= 2
    d = 3
    while d * d <= n:
        if n % d == 0:
            s.add(d)
            while n % d == 0:
                n //= d
        d += 2
    if n > 1:
        s.add(n)
    return frozenset(s)


def gen_fast(a1, nterms):
    a = [a1]
    D = [supp(a1)]
    mask = defaultdict(int)
    for p in D[0]:
        mask[p] |= 1
    full = 1
    for n in range(1, nterms + 1):
        k = a[-1] + 1
        while True:
            m = 0
            for p in supp(k):
                m |= mask[p]
                if m == full:
                    break
            if m == full:
                break
            k += 1
        a.append(k)
        D.append(supp(k))
        full = (full << 1) | 1
        for p in D[-1]:
            mask[p] |= (1 << n)
    return a, D


def minimize(cand):
    s = sorted(set(cand), key=len)
    out = []
    for P in s:
        if not any(Q <= P for Q in out):
            out.append(P)
    return out


a1 = 15015
NT = 2500
a, D = gen_fast(a1, NT)
F = minimize([frozenset([p]) for p in D[0]])
changes = []
for n in range(2, NT + 1):
    Dn = D[n - 1]
    cand = []
    for P in F:
        if P & Dn:
            cand.append(P)
        else:
            for q in Dn:
                cand.append(P | {q})
    F2 = minimize(cand)
    if F2 != F:
        changes.append(n)
    F = F2
    if n % 250 == 0:
        print("n=%-5d |F|=%-3d maxsize=%-4d minsize=%-2d  #chg=%d last=%s" %
              (n, len(F), max(len(P) for P in F), min(len(P) for P in F),
               len(changes), changes[-1] if changes else None))
print("TOTAL changes:", len(changes), "last:", changes[-1] if changes else None)
print("changes > 1200:", [c for c in changes if c > 1200])
print("final F sizes:", sorted(len(P) for P in F))
print("final F:", sorted(sorted(P) for P in F)[:10])
