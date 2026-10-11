#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""对抗性核对 10-tcl-proof.md：引理 2.1 / 3.1 / 4.1 / 4.2 / 5.x / §6。"""
from math import gcd
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


def gen(a1, nterms):
    a = [None, a1]
    D = [None, supp(a1)]
    mask = defaultdict(int)
    for p in D[1]:
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


def kill(k, a, upto):
    for i in range(1, upto + 1):
        if gcd(k, a[i]) == 1:
            return i
    return None


def check(a1, NT=200, K=None):
    a, D = gen(a1, NT)
    if K is None:
        K = min(a[NT], 6 * a1 + 200)
    full = set(range(1, len(D)))
    # --- 引理 2.1: k>=a1, kill(k)=i<inf => a_i < k
    bad21 = []
    for k in range(a1, K + 1):
        i = kill(k, a, NT)
        if i is not None and not (a[i] < k):
            bad21.append((k, i, a[i]))
    # --- A_inf ∩ [2,K]
    hits = [k for k in range(2, K + 1) if all(supp(k) & D[i] for i in range(1, len(D)))]
    hs = set(hits)
    M = [k for k in hits if not any(k2 != k and k % k2 == 0 for k2 in hits)]
    # --- 定理 5.1: 无平方因子 + 素因子 <= 2a1
    badsq = [m for m in M if any(m % (p * p) == 0 for p in supp(m))]
    badpf = [m for m in M if max(supp(m)) > 2 * a1]
    # --- 引理 3.1 / 4.1 私有指标
    badpi = []
    for m in M:
        T = supp(m)
        for p in T:
            if not any(D[i] & T == {p} for i in range(1, len(D))):
                badpi.append((m, p))
    # --- 引理 4.1: nu>2a1, p|nu => exists nu' in M: p|nu', nu' < nu/p
    bad41 = []
    for m in M:
        if m > 2 * a1:
            for p in supp(m):
                if not any(p in supp(m2) and m2 < m / p for m2 in M):
                    bad41.append((m, p))
    # --- 定理 5.3 的实现引理 5.2 界限 t < 2a1^2
    bad52 = []
    for m in M:
        t = next((i for i in range(1, len(D)) if D[i] == supp(m)), None)
        if t is None or not (t < 2 * a1 * a1):
            bad52.append((m, t))
    # --- §6 的周期结论直接核对
    L = 1
    for m in M:
        L = L * m // gcd(L, m)
    Lp1 = (L + 1) in hs
    badper = []
    for x in range(2, K - L):
        if ((x in hs) != ((x + L) in hs)):
            badper.append(x)
    print("a1=%-6d |M|=%-3d maxM=%-6s  bad21=%d badsq=%d badpf=%d badpi=%d bad41=%d bad52=%d L+1inA=%s badper=%d"
          % (a1, len(M), max(M) if M else None, len(bad21), len(badsq), len(badpf),
             len(badpi), len(bad41), len(bad52), Lp1, len(badper)))
    for nm, b in [("2.1", bad21), ("sq", badsq), ("pf", badpf), ("pi", badpi), ("4.1", bad41), ("5.2", bad52)]:
        if b:
            print("     FIRST FAIL", nm, b[:4])
    return M


for a1 in [2, 3, 4, 6, 9, 10, 12, 15, 20, 30, 35, 42, 45, 70, 77, 105, 143, 165, 195, 210, 231, 315, 385, 455, 1001, 1155, 3003]:
    check(a1, NT=120)
