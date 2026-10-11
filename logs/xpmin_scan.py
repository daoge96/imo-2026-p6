"""扫描 x_p^min := min{ z in A_inf : p | z } 与 2a1 的关系。
若存在 x_p^min > 2a1, 打印其全部细节 (m=x/p, i=kill(m), a_i, 是否 m in A_inf).
用法: python xpmin_scan.py LO HI [B_mult]
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

def build(a1, B):
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
    terms = [a1]
    while True:
        k = x + 1
        while k <= B and alive[k] == 0:
            k += 1
        if k > B:
            break
        terms.append(k); add(k); x = k
    return spf, alive, terms

def main():
    lo, hi = int(sys.argv[1]), int(sys.argv[2])
    Bm = float(sys.argv[3]) if len(sys.argv) > 3 else 4.0
    worst = (0.0, None, None)
    bad = []
    for a1 in range(lo, hi + 1):
        B = int(Bm * a1) + 60
        spf, alive, terms = build(a1, B)
        primes = [p for p in range(2, B + 1) if spf[p] == p]
        for p in primes:
            # smallest alive multiple of p
            k = p
            while k <= B and alive[k] == 0:
                k += p
            if k > B:
                continue
            r = k / (2 * a1)
            if r > worst[0]:
                worst = (r, a1, p, k)
            if k > 2 * a1:
                m = k // p
                # kill(m)
                i = None
                for t, at in enumerate(terms, 1):
                    if gcd(at, m) == 1:
                        i = t; break
                bad.append((a1, p, k, m, i, terms[i-1] if i else None, alive[m] if m <= B else None))
    print("max x_p^min/(2a1) =", worst)
    print("count x_p^min > 2a1 :", len(bad))
    seen = set()
    for row in bad[:60]:
        key = row[0]
        if key in seen: continue
        seen.add(key)
        print("a1=%d p=%d x=%d m=%d i=%s a_i=%s m_in_Ainf=%s" % row)

main()
