"""检验 (c') tau_p <= a1/p  (等价 x_p^min = p*tau_p <= a1) 是否在 p∤a1 时成立.
tau_p := min{ s>=1 : supp(s) 与所有 p∤a_s 的 D_s 相交 }  (即 x_p^min = p*tau_p 的 tau).
用法: python lead_tau.py LO HI [TOPN]
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
    topn = int(sys.argv[3]) if len(sys.argv) > 3 else 10
    rows, viol = [], []
    n = 0
    for a1 in range(lo, hi + 1):
        B = 6 * a1 + 80
        spf, M, terms = build(a1, B)
        Ep = {}
        for mu in M:
            for p in supp(mu, spf):
                Ep.setdefault(p, mu)
        for p, sigma in Ep.items():
            t = sigma // p
            # tau_p: smallest s >= 2 with supp(s) meeting every p-free term support
            tau = None
            for s in range(2, sigma + 1):
                S = set(supp(s, spf))
                if all(S & set(supp(ts, spf)) for ts in terms if ts % p != 0):
                    tau = s; break
            if tau is None:
                continue
            n += 1
            xmin = p * tau
            r = xmin / a1
            rows.append((r, a1, p, sigma, t, tau))
            if p * tau > a1:
                viol.append((a1, p, sigma, t, tau))
    rows.sort(reverse=True)
    print("instances:", n, " violations of p*tau <= a1 :", len(viol))
    for r in rows[:topn]:
        print("xmin/a1=%.3f a1=%d p=%d sigma=%d t=%d tau=%d" % r)
    if viol[:10]:
        print("viol:", viol[:10])

main()
