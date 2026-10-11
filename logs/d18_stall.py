"""d18_stall.py -- 检验 stall 支目标 p*nu_q <= a1*q (prover-descent, task-12).

stall 支已证 mu* = nu_q (见 16 号 §11), 故 stall 目标等价于 p*nu_q <= a1*q
等价于 p*t_q <= a1 (nu_q = q*t_q).
用法: python d18_stall.py LO HI
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
    spf = spf_sieve(B)
    alive = bytearray([1]) * (B + 1)
    alive[0] = 0
    alive[1] = 0
    stamp = [0] * (B + 1)
    tid = 0

    def add(v):
        nonlocal tid
        tid += 1
        for q in supp(v, spf):
            for j in range(q, B + 1, q):
                stamp[j] = tid
        for j in range(2, B + 1):
            if alive[j] and stamp[j] != tid:
                alive[j] = 0

    add(a1)
    terms = [a1]
    x = a1
    while True:
        k = x + 1
        while k <= B and not alive[k]:
            k += 1
        if k > B:
            break
        terms.append(k)
        add(k)
        x = k
    M = []
    for k in range(2, B + 1):
        if alive[k] and not any(k % m == 0 for m in M):
            M.append(k)
    return spf, alive, terms, M

def main():
    lo, hi = int(sys.argv[1]), int(sys.argv[2])
    n = 0
    bad = []
    worst = (0.0,)
    worst_gap = (0.0,)
    for a1 in range(lo, hi + 1):
        B = 6 * a1 + 60
        spf, alive, terms, M = build(a1, B)
        D1 = set(supp(a1, spf))
        for p in sorted({q for mu in M for q in supp(mu, spf)}):
            sigma = min(mu for mu in M if mu % p == 0)
            t = sigma // p
            for q in [x for x in supp(t, spf) if x in D1]:
                n += 1
                nu_q = min(mu for mu in M if mu % q == 0)
                lhs = p * nu_q
                rhs = a1 * q
                r = lhs / rhs
                if r > worst[0]:
                    worst = (r, a1, p, q, nu_q)
                if lhs > rhs:
                    bad.append((a1, p, q, nu_q, lhs, rhs))
                g = p * (nu_q // q) / a1
                if g > worst_gap[0]:
                    worst_gap = (g, a1, p, q, nu_q)
    print("(a1,p,q) with q in Q_p:", n)
    print("p*nu_q > a1*q 的反例数:", len(bad), bad[:10])
    print("max p*nu_q/(a1 q) =", worst)
    print("max p*t_q/a1 =", worst_gap)

main()
