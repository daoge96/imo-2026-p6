"""d16_tscan.py -- 检验 §5 引理 16.12(i) 的关键子断言 (prover-descent).

对每个 (a1,p), E_p 非空, sigma=nu_p, t=sigma/p:
   是否存在 d | t, d>=2, d in A_inf ?
若存在: 打印 (a1,p,sigma,t,d) 与 pd 是否 < sigma, 以及 E_p 的最小元.
用法: python d16_tscan.py LO HI
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

def in_Ainf(d, a1, alive, terms):
    """d>=2 是否在 A_inf. d>=a1 时 alive 判定精确; d<a1 时用 kill 扫描 (可能过高估计)."""
    if d >= a1:
        return bool(alive[d]), "exact"
    for at in terms:
        if gcd(at, d) == 1:
            return False, "killed"
    return True, "no-killer(<a1, 可能虚高)"

def main():
    lo, hi = int(sys.argv[1]), int(sys.argv[2])
    hits = []
    nE = 0
    for a1 in range(lo, hi + 1):
        B = 6 * a1 + 60
        spf, alive, terms, M = build(a1, B)
        primes = sorted({p for mu in M for p in supp(mu, spf)})
        for p in primes:
            nE += 1
            sigma = min(mu for mu in M if mu % p == 0)
            t = sigma // p
            for d in range(2, t + 1):
                if t % d:
                    continue
                ok, why = in_Ainf(d, a1, alive, terms)
                if ok:
                    hits.append((a1, p, sigma, t, d, why, sigma - p * d))
    print("(a1,p) with E_p nonempty:", nE)
    print("存在 d|t, d>=2, d in A_inf 的实例数:", len(hits))
    for row in hits[:40]:
        print("   a1=%d p=%d sigma=%d t=%d d=%d [%s] sigma-pd=%d" % row)

main()
