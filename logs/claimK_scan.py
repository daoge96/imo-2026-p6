"""检验 Claim K: 若 p 整除某极小元, 则 min{mu in M: p|mu} <= min{y in A_inf: p|y}.
用法: python claimK_scan.py LO HI [B_mult]
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
    return spf, alive, M

def main():
    lo, hi = int(sys.argv[1]), int(sys.argv[2])
    Bm = float(sys.argv[3]) if len(sys.argv) > 3 else 4.0
    viol = []
    checked = 0
    for a1 in range(lo, hi + 1):
        B = int(Bm * a1) + 60
        spf, alive, M = build(a1, B)
        primes = set()
        for mu in M:
            primes |= set(supp(mu, spf))
        for p in primes:
            ymin = None
            k = p
            while k <= B:
                if alive[k]:
                    ymin = k; break
                k += p
            if ymin is None:
                continue
            mmin = min([mu for mu in M if mu % p == 0])
            checked += 1
            if mmin > ymin:
                viol.append((a1, p, mmin, ymin))
    print("checked pairs:", checked, "violations:", len(viol))
    for row in viol[:40]:
        print("a1=%d p=%d minE_p=%d minAinf_p=%d" % row)

main()
