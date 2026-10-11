"""d16_probe.py -- 独立数值探针 (prover-descent).

目标:
 (A) 每个极小元 mu 的 mu/(2a1) 最大值 / 是否存在 mu>2a1;
 (B) 每个 (mu,p) 对的 w=mu/p 与 a1 的比较 (即 H_p 是否成立);
 (C) 下降构造的自检: i=kill(w), nu'=min{M 中整除 rad(a_i) 者};
     检查 nu' < w, p|nu', supp(nu') ∩ supp(mu) = {p} 是否总成立;
 (D) 记录 "坏情形" a_i >= mu (即位置引理失效的情形) 的全部细节.

方法: 直接模拟序列到 B = mult*a1; alive[k] <=> k 与所有已处理项不互素.
对 k >= a1, k in A_inf <=> alive[k] (位置引理: 杀手项 < k).
用法: python d16_probe.py LO HI [mult] [topN]
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
    # M: 极小 alive 元
    M = []
    for k in range(2, B + 1):
        if alive[k] and not any(k % m == 0 for m in M):
            M.append(k)
    return spf, alive, terms, M

def main():
    lo = int(sys.argv[1]); hi = int(sys.argv[2])
    mult = float(sys.argv[3]) if len(sys.argv) > 3 else 6.0
    topN = int(sys.argv[4]) if len(sys.argv) > 4 else 5
    worst = (0.0, None, None)          # max mu/(2a1)
    worstH = (0.0, None, None, None)   # max mu/(a1*p) -> 记录 mu/p 与 a1 之比
    bad_mu = []                        # mu > 2a1
    badH = []                          # 存在 p: mu/p >= a1
    badcons = []                       # 构造检查失败
    badcase = []                       # a_i >= mu (位置引理不适用)
    ncase = 0
    for a1 in range(lo, hi + 1):
        B = int(mult * a1) + 60
        spf, alive, terms, M = build(a1, B)
        for mu in M:
            ncase += 1
            if mu > 2 * a1:
                bad_mu.append((a1, mu))
            if mu / (2 * a1) > worst[0]:
                worst = (mu / (2 * a1), a1, mu)
            for p in supp(mu, spf):
                w = mu // p
                if w / a1 > worstH[0]:
                    worstH = (w / a1, a1, mu, p)
                if w >= a1:
                    badH.append((a1, mu, p, w))
                if w < 2:
                    continue
                # i = kill(w)
                i = None
                for t, at in enumerate(terms, 1):
                    if gcd(at, w) == 1:
                        i = t; break
                if i is None:
                    badcons.append(("no-kill", a1, mu, p, w, None))
                    continue
                ai = terms[i - 1]
                if ai >= mu:
                    badcase.append((a1, mu, p, w, i, ai))
                rad = 1
                for q in supp(ai, spf):
                    rad *= q
                cand = [m for m in M if rad % m == 0]
                if not cand:
                    badcons.append(("no-divisor", a1, mu, p, w, ai))
                    continue
                nu1 = min(cand)
                ok1 = (nu1 % p == 0)
                ok2 = (sorted(set(supp(nu1, spf)) & set(supp(mu, spf))) == [p])
                ok3 = (nu1 < w)
                if not (ok1 and ok2 and ok3):
                    badcons.append(("fail", a1, mu, p, w, ai, nu1, ok1, ok2, ok3))
    print("cases(mu count):", ncase, " a1 in [%d,%d]" % (lo, hi))
    print("max mu/(2a1) =", worst)
    print("count mu>2a1:", len(bad_mu), bad_mu[:10])
    print("max (mu/p)/a1 =", worstH)
    print("count (mu,p) with mu/p>=a1 [H_p]:", len(badH), badH[:10])
    print("count kill-term >= mu (位置引理不适用):", len(badcase))
    for row in badcase[:topN]:
        print("   badcase a1=%d mu=%d p=%d w=%d i=%d a_i=%d" % row)
    print("count 构造失败:", len(badcons))
    for row in badcons[:topN]:
        print("   ", row)

main()
