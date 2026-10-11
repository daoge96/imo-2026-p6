"""找出 p/a1 最大的非平凡实例 (t>=2), 观察机制.
用法: python lead_pa1tight.py LO HI [TOPN]
"""
import sys

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

def analyze(a1, B):
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
    M = []
    for k in range(2, B + 1):
        if alive[k] and not any(k % m == 0 for m in M):
            M.append(k)
    return spf, M, terms

def main():
    lo, hi = int(sys.argv[1]), int(sys.argv[2])
    topn = int(sys.argv[3]) if len(sys.argv) > 3 else 15
    rows = []
    for a1 in range(lo, hi + 1):
        B = 6 * a1 + 80
        spf, M, terms = analyze(a1, B)
        D1 = set(supp(a1, spf))
        Ep = {}
        for mu in M:
            for p in supp(mu, spf):
                Ep.setdefault(p, mu)
        for p, sigma in Ep.items():
            t = sigma // p
            if t < 2:
                continue
            Q = [q for q in supp(t, spf) if q in D1]
            rows.append((p / a1, a1, p, sigma, t, Q, sorted(D1)))
    rows.sort(reverse=True)
    print("非平凡实例数 (t>=2):", len(rows))
    for r in rows[:topn]:
        print("p/a1=%.4f a1=%d p=%d sigma=%d t=%d Q=%s D1=%s" % r)

main()
