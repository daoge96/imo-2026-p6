"""d17_kill: 测量 (CS)-论证中缺口所需的量：mu/r < a1 时 a_{i_r} 的上界。

对每个 a1<=HI、每个 mu in M、每个 r | mu 且 mu/r < a1：
  i_r := kill(mu/r)（线性扫描已生成的项），记录 ratio = a_{i_r} * r / mu（即 a_{i_r} 相对 mu/r 的倍数）
统计 max ratio 与 argmax；另统计 mu/r >= a1 时 ratio 是否 <1（超引理自检）。
用法: python d17_kill.py HI [mult]
"""
import sys, time
from math import gcd

def sieve(n):
    spf = list(range(n + 1))
    i = 2
    while i * i <= n:
        if spf[i] == i:
            for j in range(i * i, n + 1, i):
                if spf[j] == j:
                    spf[j] = i
        i += 1
    return spf

LIM = 4_000_000
SPF = sieve(LIM)

def fac(n):
    s = []
    while n > 1:
        p = SPF[n] if n <= LIM else None
        if p is None:
            d = 2
            while d * d <= n:
                if n % d == 0:
                    s.append(d)
                    while n % d == 0:
                        n //= d
                d += 1
            if n > 1:
                s.append(n)
            return s
        s.append(p)
        while n % p == 0:
            n //= p
    return s

def minimize(lst):
    out = []
    for x in sorted(set(lst)):
        if not any(x % y == 0 for y in out):
            out.append(x)
    return out

def run(a1, B):
    seq = [a1]
    Z = {q: 0 for q in fac(a1)}
    M = minimize(fac(a1))
    n = 1
    full = 1
    while seq[-1] <= B:
        k = seq[-1] + 1
        while True:
            comp = full
            x = k
            while x > 1:
                q = SPF[x]
                if q in Z:
                    comp &= Z[q]
                    if comp == 0:
                        break
                while x % q == 0:
                    x //= q
            if comp == 0:
                break
            k += 1
        D = fac(k)
        dead = [b for b in M if gcd(b, k) == 1]
        cand = [b for b in M if gcd(b, k) > 1]
        for b in dead:
            for p in D:
                cand.append(b * p)
        M = minimize(cand)
        seq.append(k)
        for q in list(Z.keys()):
            if q not in D:
                Z[q] |= (1 << n)
        for q in D:
            if q not in Z:
                Z[q] = (1 << n) - 1
        n += 1
        full = (full << 1) | 1
    return [m for m in M if m <= B], seq

def kill(k, seq):
    for i, a in enumerate(seq, 1):
        if gcd(k, a) == 1:
            return i, a
    return None, None

def main():
    HI = int(sys.argv[1]) if len(sys.argv) > 1 else 1500
    mult = float(sys.argv[2]) if len(sys.argv) > 2 else 3.0
    t0 = time.time()
    best = (0.0, 0, 0, 0, 0)     # max a_{i_r}*r/mu among 2<=mu/r<a1
    ncase = 0
    worst_ge = (0.0, 0, 0, 0, 0)    # max ratio among mu/r>=a1 （应 <=1）
    for a1 in range(2, HI + 1):
        B = int(mult * a1) + 8
        M, seq = run(a1, B)
        for mu in M:
            for r in fac(mu):
                if mu // r < 2:
                    continue
                if mu // r < a1:
                    i, ai = kill(mu // r, seq)
                    if ai is None:
                        continue
                    ncase += 1
                    ratio = ai * r / mu
                    if ratio > best[0]:
                        best = (ratio, a1, mu, r, ai)
                else:
                    i, ai = kill(mu // r, seq)
                    if ai is None:
                        continue
                    ratio = ai * r / mu
                    if ratio > worst_ge[0]:
                        worst_ge = (ratio, a1, mu, r, ai)
    print(f"[kill] a1<= {HI} cases(mu/r<a1)={ncase} elapsed={time.time()-t0:.1f}s")
    print(f"[kill] max a_(i_r)*r/mu among mu/r<a1 = {best[0]:.4f} at a1={best[1]} mu={best[2]} r={best[3]} a_i={best[4]}")
    print(f"[kill] max a_(i_r)*r/mu among mu/r>=a1 = {worst_ge[0]:.4f} at a1={worst_ge[1]} mu={worst_ge[2]} r={worst_ge[3]} a_i={worst_ge[4]}  (position lemma => 应 <1)")

main()
