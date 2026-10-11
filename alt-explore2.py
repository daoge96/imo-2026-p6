#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""探索 A_inf 的极小元集合 B —— 判定路线 2 是否可行。"""
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


def report(a1, nterms=250, K=3000):
    a, D = gen(a1, nterms)
    C = 1
    for p in D[0]:
        C *= p
    inter = set(D[0])
    for d in D:
        inter &= set(d)
    hits = [k for k in range(2, K + 1) if all(supp(k) & Di for Di in D)]
    hitset = set(hits)
    mins = [k for k in hits if not any(k2 != k and k % k2 == 0 for k2 in hits)]
    n = len(D)
    tcl = None
    for N in range(1, n):
        if all(any(D[i] <= D[m] for i in range(1, N + 1)) for m in range(N + 1, n)):
            tcl = N
            break
    print("a1=%d C=%d |P|=%-3d tclN=%-5s |B|<K: %-3d maxB=%-8s" %
          (a1, C, len(inter), tcl, len(mins), max(mins) if mins else None))
    print("    B =", mins[:18])
    print("    terms[:14] =", a[1:15])
    # 自检：每个大支撑是否含某个早期支撑
    bad = []
    for m in range(tcl or 0, n):
        if not any(D[i] <= D[m] for i in range(1, (tcl or 0) + 1)):
            bad.append(m)
    print("    |hits|=", len(hits), " bad m after tclN =", len(bad))


for a1 in [15, 35, 45, 77, 105, 143, 165, 195, 231, 315, 385, 455, 595, 715, 1001]:
    report(a1)
print("-" * 60)
for a1 in [1155, 1365, 2145, 3003, 5005, 15015]:
    report(a1, nterms=200, K=2500)
