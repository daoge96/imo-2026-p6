"""lead_Hnear.py -- H 的"接近程度"：对每个 mu in M 算 min_p mu/(p*a1)（H <=> >1）。
报告 max over mu of min_p mu/(p*a1) 及其 argmax；顺便记录 |S|, X=prod_{S\D1}p, X/a1。
用法: python lead_Hnear.py LO HI [TOPN]
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
    topn = int(sys.argv[3]) if len(sys.argv) > 3 else 10
    rows = []
    nH = 0
    for a1 in range(lo, hi + 1):
        B = 6 * a1 + 80
        spf, M = build(a1, B)
        D1 = set(supp(a1, spf))
        for mu in M:
            S = supp(mu, spf)
            r = min(mu / (p * a1) for p in S)
            if r > 1:
                nH += 1
            X = 1
            for p in S:
                if p not in D1:
                    X *= p
            rows.append((r, a1, mu, sorted(S), len(S), X / a1))
    rows.sort(reverse=True)
    print("total mu:", len(rows), " H-instances:", nH)
    print("max over mu of min_p mu/(p*a1):")
    for r in rows[:topn]:
        print("  ratio=%.4f a1=%d mu=%d S=%s |S|=%d X/a1=%.4f" % r)

main()
