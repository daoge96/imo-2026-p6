#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""独立第二路线（prover-alt）的数值探索脚本；只用于定位命题。"""
from math import gcd
from collections import Counter


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


def kill(k, a):
    for i, x in enumerate(a, 1):
        if gcd(k, x) == 1:
            return i
    return None


def tcl_N(D):
    n = len(D)
    for N in range(1, n):
        if all(any(D[i] <= D[m] for i in range(1, N + 1)) for m in range(N + 1, n)):
            return N
    return None


def Ainf_members(D, K):
    out = []
    for k in range(2, K + 1):
        sk = supp(k)
        if all(sk & Di for Di in D):
            out.append(k)
    return out


for a1 in [2, 3, 4, 6, 9, 10, 12, 15, 20, 30, 35, 42, 45, 70, 105, 210]:
    a, D = gen(a1, 70)
    C = 1
    for p in D[0]:
        C *= p
    cnt = Counter(gcd(a[m], C) for m in range(1, len(a)))
    print("=" * 66)
    print("a1 =", a1, "  C=rad(a1) =", C, "  D1 =", sorted(D[0]))
    print("  terms[:16] =", a[1:16])
    print("  dist of gcd(a_m,C):", dict(cnt))
    print("  min TCL N =", tcl_N(D))
    K = 4 * C + 60
    mem = Ainf_members(D, K)
    mins = [k for k in mem if not any(k2 != k and k % k2 == 0 for k2 in mem)]
    print("  minimal elts of A_inf in [2,%d]:" % K, mins[:30])
    print("  |A_inf int [2,K]| =", len(mem), " with K =", K)
