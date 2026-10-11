#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""追踪 F_n 的最后改变时刻（Main Lemma 等价于 F_n 稳定）。"""
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


def run(a1, nterms):
    a, D = gen(a1, nterms)
    F = minimize([frozenset([p]) for p in D[0]])
    changes = []
    maxF = len(F)
    for n in range(2, nterms + 1):
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
        maxF = max(maxF, len(F))
    print("a1=%-7d nterms=%-5d changes=%-4d last=%-6s |F|final=%-3d max|F|=%-4d maxsize=%d" %
          (a1, nterms, len(changes), changes[-1] if changes else None,
           len(F), maxF, max(len(P) for P in F)))
    print("      last 12 change steps:", changes[-12:])


for a1, nt in [(15015, 600), (3003, 600), (385, 600), (1155, 600), (255255, 400), (46410, 400), (510510, 300)]:
    run(a1, nt)
