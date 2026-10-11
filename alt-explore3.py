#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""检验：F_n（D_1..D_n 的极小横截集族）是否稳定。稳定 <=> Main Lemma。"""
from math import gcd


def supp(n):
    s = set()
    d = 2
    while d * d <= n:
        if n % d == 0:
            s.add(d)
            while n % d == 0:
                n //= d
        d += 1
    if n > 1:
        s.add(n)
    return frozenset(s)


def gen(a1, nterms):
    a = [a1]
    D = [supp(a1)]
    for _ in range(nterms):
        k = a[-1] + 1
        while True:
            sk = supp(k)
            if all(sk & Di for Di in D):
                break
            k += 1
        a.append(k)
        D.append(sk)
    return a, D


def minimize(cand):
    s = sorted(set(cand), key=len)
    out = []
    for P in s:
        if not any(Q <= P for Q in out):
            out.append(P)
    return out


def Fseq(a1, nterms):
    a, D = gen(a1, nterms)
    F = [frozenset([p]) for p in D[0]]
    F = minimize(F)
    stab = None
    prev = None
    dat = []
    for n in range(2, nterms + 1):
        Dn = D[n - 1]
        cand = []
        for P in F:
            if P & Dn:
                cand.append(P)
            else:
                for q in Dn:
                    cand.append(P | {q})
        F = minimize(cand)
        dat.append((n, len(F), max(len(P) for P in F)))
        if prev is not None and F == prev and stab is None:
            stab = n - 1
        prev = F
    return a, D, F, stab, dat


for a1 in [15, 35, 45, 77, 105, 143, 165, 195, 231, 315, 385, 455, 1001, 1155, 15015]:
    a, D, F, stab, dat = Fseq(a1, 400)
    grow = [d for d in dat if d[1] > 30]
    print("a1=%-6d stabilize at n0=%-5s |F|=%-3d maxsize=%-2d  (max|F| seen=%d)" %
          (a1, stab, len(F), max(len(P) for P in F), max(d[1] for d in dat)))
    print("      F =", sorted(sorted(P) for P in F)[:12])
    # 稳定后核对：每个 m>n0 是否含某个 F 的元素
    if stab:
        ok = all(any(P <= D[m] for P in F) for m in range(stab + 1, len(D)))
        print("      after stab, all D_m contain some P in F:", ok)
