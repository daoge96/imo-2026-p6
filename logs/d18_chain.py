"""d18_chain.py -- 检验 (b) 攻击中的"夹逼/链"步骤 (prover-descent, task-10).

对每个 (a1,p) with E_p != empty, sigma=nu_p, t=sigma/p:
  对每个 q | t 且 q | a1 且 sigma > a1*q (16.4 可用):
    取 nu_q = min E_q；检查 (i) supp(nu_q) ∩ supp(sigma) = {q};
    (ii) nu_q < sigma/q; (iii) nu_q <= p*nu_q 平凡; (iv) t <= nu_q ? (夹逼)
    (v) q < p ?
用法: python d18_chain.py LO HI
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
    ncases = 0
    bad_supp, bad_lt, bad_sq, bad_qp = [], [], [], []
    worst_t_over_nuq = (0.0,)
    for a1 in range(lo, hi + 1):
        B = 6 * a1 + 60
        spf, alive, terms, M = build(a1, B)
        D1 = set(supp(a1, spf))
        for p in sorted({q for mu in M for q in supp(mu, spf)}):
            sigma = min(mu for mu in M if mu % p == 0)
            t = sigma // p
            for q in supp(t, spf):
                if q not in D1:
                    continue
                if not (sigma > a1 * q):
                    continue
                ncases += 1
                E_q = [mu for mu in M if mu % q == 0]
                if not E_q:
                    bad_supp.append(("no E_q", a1, p, q))
                    continue
                nu_q = min(E_q)
                if not (set(supp(nu_q, spf)) & set(supp(sigma, spf)) == {q}):
                    bad_supp.append(("supp", a1, p, q, sigma, nu_q))
                if not (nu_q < sigma / q):
                    bad_lt.append((a1, p, q, sigma, nu_q))
                if t > nu_q:
                    bad_sq.append((a1, p, q, t, sigma, nu_q))
                if not (q < p):
                    bad_qp.append((a1, p, q))
                r = t / nu_q
                if r > worst_t_over_nuq[0]:
                    worst_t_over_nuq = (r, a1, p, q, t, nu_q)
    print("可用 (16.4 前提成立) 的三元组 (a1,p,q) 数:", ncases)
    print("supp 夹逼失败:", len(bad_supp), bad_supp[:5])
    print("nu_q < sigma/q 失败:", len(bad_lt), bad_lt[:5])
    print("t <= nu_q 失败 (夹逼失效):", len(bad_sq), bad_sq[:10])
    print("q < p 失败:", len(bad_qp), bad_qp[:5])
    print("max t/nu_q =", worst_t_over_nuq)

main()
