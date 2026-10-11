"""检验强不变量: 对 mu in M, p|mu 是否有 mu/p <= rad(a1) (或 <= a1).
用法: python cofactor_scan.py LO HI [B_mult]
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

def analyze(a1, mult=3, extra=60):
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
    Bm = float(sys.argv[3]) if len(sys.argv) > 3 else 3.0
    worst_a1 = (0.0, None, None, None)   # mu/(p*a1)
    worst_rad = (0.0, None, None, None)  # mu/(p*rad(a1))
    viol_a1 = []
    viol_rad = []
    for a1 in range(lo, hi + 1):
        spf, M = analyze(a1, mult=Bm)
        rad = 1
        for p in supp(a1, spf):
            rad *= p
        for mu in M:
            for p in supp(mu, spf):
                cof = mu // p
                if cof / (a1) > worst_a1[0]:
                    worst_a1 = (cof / a1, a1, mu, p)
                if cof / rad > worst_rad[0]:
                    worst_rad = (cof / rad, a1, mu, p)
                if cof > a1:
                    viol_a1.append((a1, mu, p, cof))
                if cof > rad:
                    viol_rad.append((a1, mu, p, cof, rad))
    print("max (mu/p)/a1 =", worst_a1)
    print("max (mu/p)/rad(a1) =", worst_rad)
    print("violations cof > a1 :", len(viol_a1), viol_a1[:12])
    print("violations cof > rad(a1) :", len(viol_rad), viol_rad[:12])

main()
