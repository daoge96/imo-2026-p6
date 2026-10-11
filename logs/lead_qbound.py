"""检查 prover-descent 暂停前报告的线索: sigma = nu_p <= a1*q 对某个 q|t, q|a1 (q 素数).
若成立则 p = sigma/t <= a1*q/t <= a1 (因 q<=t) => 路线 (b) 得证 => 闭环.
用法: python lead_qbound.py LO HI [mult]
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

def analyze(a1, mult=4, extra=80):
    B = int(mult * a1) + extra
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
    mult = float(sys.argv[3]) if len(sys.argv) > 3 else 4.0
    viol, checked, worst = [], 0, (0.0, None, None, None, None)
    for a1 in range(lo, hi + 1):
        spf, M = analyze(a1, mult)
        D1 = set(supp(a1, spf))
        Ep = {}
        for mu in M:
            for p in supp(mu, spf):
                Ep.setdefault(p, mu)
        for p, sigma in Ep.items():
            t = sigma // p
            Q = [q for q in supp(t, spf) if q in D1]
            if not Q:
                viol.append((a1, p, sigma, "Q empty")); continue
            best = min(a1 * q / sigma for q in Q)
            checked += 1
            if best > worst[0]:
                worst = (best, a1, p, sigma, Q)
            if all(sigma > a1 * q for q in Q):
                viol.append((a1, p, sigma, Q))
    print("checked (a1,p) pairs:", checked)
    print("worst min_q a1*q/sigma =", worst)
    print("violations of  exists q|t,q|a1: sigma<=a1*q :", len(viol), viol[:10])

main()
