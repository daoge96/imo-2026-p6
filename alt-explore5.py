#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""快速版：追踪 F_n 的最后改变时刻（Main Lemma <=> F_n 稳定）。"""
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


def run(a1, nterms):
    a, D = gen_fast(a1, nterms)
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
    print("a1=%-7d nterms=%-5d #changes=%-4d last=%-6s |F|fin=%-3d max|F|=%-4d" %
          (a1, nterms, len(changes), changes[-1] if changes else None, len(F), maxF))
    print("      last 15 change steps:", changes[-15:])
    print("      min-size in F:", min(len(P) for P in F), " max-size:", max(len(P) for P in F))


for a1, nt in [(15015, 500), (15015, 1200), (3003, 1500), (385, 1000), (1155, 1000)]:
    run(a1, nt)
