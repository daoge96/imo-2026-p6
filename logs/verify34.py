"""verify34.py -- 在我们自己的语言下核验"补强引理"（33 引理 3.1 的等价形式）：

  (LP) 若项 a_t 含素因子 p > a1^2，则存在 j < t 使 supp(a_j) ⊆ supp(a_t).

同时核验由它 + 我们的"μ∈M <=> supp(μ) 极小横截"推出的结论：
  (FME*) 每个 A_∞-极小元的支撑只含 <= a1^2 的素因子.

用法: python verify34.py [B]
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

def _supp(x, spf):
    out = []
    while x > 1:
        p = spf[x]
        out.append(p)
        while x % p == 0:
            x //= p
    return out

def build(a1, B, spf):
    alive = bytearray([1]) * (B + 1)
    alive[0] = alive[1] = 0
    for j in range(2, a1):
        alive[j] = 0
    terms = []
    cur = a1
    while True:
        k = cur + 1
        while k <= B and not alive[k]:
            k += 1
        if k > B:
            break
        terms.append(k)
        for y in range(k + 1, B + 1):
            if alive[y] and gcd(y, k) == 1:
                alive[y] = 0
        cur = k
    return terms

def is_minimal_element(t, terms, D1):
    """t 是否为 A_∞-极小元（窗口内）：t 无平方因子、supp(t) 横截(窗口内)、无真因子同样横截."""
    S = set(_supp(t, spf_global))
    if len(S) != len(_supp(t, spf_global)):
        return False, S
    # 窗口内横截：与每个项相交
    for a in terms:
        if not (S & set(_supp(a, spf_global))):
            return False, S
    # 无真因子横截
    for p in S:
        T = S - {p}
        if T and all(T & set(_supp(a, spf_global)) for a in terms):
            return False, S
    return True, S

def main():
    global spf_global
    B = int(sys.argv[1]) if len(sys.argv) > 1 else 3000
    spf_global = spf_sieve(B + 1)
    cases = [2, 3, 4, 6, 12, 15, 30, 35, 45, 99, 121, 175, 187, 899]
    allok = True
    for a1 in cases:
        if a1 > B // 2:
            continue
        terms = build(a1, B, spf_global)
        sup = [set(_supp(t, spf_global)) for t in terms]
        lp_bad = []
        for i, t in enumerate(terms):
            if any(p > a1 * a1 for p in sup[i]):
                if not any(sup[j] <= sup[i] for j in range(i)):
                    lp_bad.append(t)
        # FME*: 窗口内极小元 -> 支撑只含小素因子
        fme_bad = []
        for t in terms:
            ok, S = is_minimal_element(t, terms, None)
            if ok and any(p > a1 * a1 for p in S):
                fme_bad.append((t, sorted(S)))
        allok &= (not lp_bad) and (not fme_bad)
        print("a1=%-4d terms=%-5d  (LP)违例=%d  (FME*)违例=%d  %s"
              % (a1, len(terms), len(lp_bad), len(fme_bad), "OK" if not (lp_bad or fme_bad) else "FAIL"))
        if lp_bad[:3]:
            print("     LP e.g.:", lp_bad[:3])
        if fme_bad[:3]:
            print("     FME* e.g.:", fme_bad[:3])
    print("ALL:", "OK" if allok else "FAIL")

main()
