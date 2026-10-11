"""找出 mu/a1 最大的样本, 观察结构。
用法: python top_ratio.py LO HI [TOPN]
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

def supp(x, spf):
    out = []
    while x > 1:
        p = spf[x]
        out.append(p)
        while x % p == 0:
            x //= p
    return out

def analyze(a1, mult=3, extra=60):
    B = mult * a1 + extra
    spf = spf_sieve(B + 1)
    alive = bytearray([1]) * (B + 2)
    alive[0] = 0; alive[1] = 0
    stamp = [0] * (B + 2)
    st = [0]
    def add(v):
        st[0] += 1
        t = st[0]
        for q in supp(v, spf):
            for j in range(q, B + 1, q):
                stamp[j] = t
        for j in range(2, B + 1):
            if alive[j] and stamp[j] != t:
                alive[j] = 0
    add(a1)
    x = a1
    while True:
        k = x + 1
        while k <= B and alive[k] == 0:
            k += 1
        if k > B:
            break
        add(k); x = k
    M = []
    for k in range(2, B + 1):
        if alive[k] and not any(k % m == 0 for m in M):
            M.append(k)
    return spf, M

def main():
    lo, hi = int(sys.argv[1]), int(sys.argv[2])
    topn = int(sys.argv[3]) if len(sys.argv) > 3 else 15
    rows = []
    for a1 in range(lo, hi + 1):
        spf, M = analyze(a1)
        for mu in M:
            rows.append((mu / a1, a1, mu, supp(mu, spf), supp(a1, spf)))
    rows.sort(reverse=True)
    for r in rows[:topn]:
        print("mu/a1=%.4f a1=%d mu=%d supp(mu)=%s supp(a1)=%s" % r)

main()
