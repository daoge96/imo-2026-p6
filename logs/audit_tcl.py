"""对抗性复核 10-tcl-proof.md：
(V1) 引理2.1: k>=a1 且 kill(k)=i<inf  =>  a_i < k
(V2) 引理4.2: 所有极小元的素因子 <= 2a1
(V3) 引理5.2: 其不等式 mu*p^(e-1) < a1 是否成立；t < 2a1^2 是否成立
(V4) 定理5.1/§6: 极小元集合 + a_{n+T}=a_n+L 的暴力核对
"""
import sys
sys.path.insert(0, r"D:\OneDrive\Desktop\dsh\imo-p6\logs")
from math import gcd
from fme_exp2 import build, factor

def kill(seq, k):
    for i, a in enumerate(seq, 1):
        if gcd(k, a) == 1:
            return i
    return None

def check(a1, nmax, kbound):
    r = build(a1, nmax)
    seq = r["seq"]
    pers = sorted(set(r["hist"][nmax // 2]) & set(r["hist"][nmax]))
    out = {}
    # V1
    bad1 = []
    for k in range(a1, kbound):
        i = kill(seq, k)
        if i is not None and seq[i - 1] >= k:
            bad1.append((k, i, seq[i - 1]))
    out["bad_2.1"] = bad1[:5]
    # V2
    bad2 = [(b, max(factor(b))) for b in pers if max(factor(b)) > 2 * a1]
    out["bad_4.2"] = bad2[:5]
    # V3
    bad3, bad3b, ratios = [], [], []
    idx = {v: i + 1 for i, v in enumerate(seq)}
    for mu in pers:
        for p in factor(mu):
            e = 1
            while mu * p ** e < a1:
                e += 1
            lhs = mu * p ** (e - 1)
            if lhs >= a1:
                bad3.append((mu, p, e, lhs, a1))
            k = mu * p ** e
            t = idx.get(k) or kill(seq, k)
            if t is None or t >= 2 * a1 * a1:
                bad3b.append((mu, p, k, t))
            ratios.append((t or 0, a1, mu, p, k))
    out["bad_5.2_ineq"] = bad3[:5]
    out["bad_5.2_concl"] = bad3b[:5]
    out["maxt_over_2a1sq"] = max((t / (2 * a1 * a1) for t, *_ in ratios), default=0)
    out["maxmu_over_a1"] = max((b / a1 for b in pers), default=0)
    out["maxmu_over_2a1"] = max((b / (2 * a1) for b in pers), default=0)
    out["maxmu_over_a1rad"] = max((b / (a1 * max(factor(a1))) for b in pers), default=0)
    out["mu"] = pers
    return out

def period_check(a1, nmax):
    """V4: 由 A_inf 极小元构造 L,T 并核对 a_{n+T}=a_n+L 对全部 n 成立"""
    r = build(a1, nmax)
    seq = r["seq"]
    pers = sorted(set(r["hist"][nmax // 2]) & set(r["hist"][nmax]))
    L = 1
    for mu in pers:
        L = L * mu // gcd(L, mu)
    A = set()
    for k in range(2, L + 1):
        if any(k % mu == 0 for mu in pers):
            A.add(k)
    T = len(A)
    # check periodicity of A_inf membership on a window
    ok = True
    for k in range(2, 3000):
        if (any(k % mu == 0 for mu in pers)) != (any((k + L) % mu == 0 for mu in pers)):
            ok = False
    # check a_{n+T} = a_n+L for all n with n+T <= len(seq)
    ok2 = all(seq[n - 1 + T] == seq[n - 1] + L for n in range(1, len(seq) - T + 1))
    return L, T, ok, ok2, seq[:3]

def main():
    worst = []
    for a1 in list(range(2, 130)) + [150, 187, 210, 385, 1001, 2310, 3003, 15015]:
        nmax = 300 if a1 > 1000 else 400
        o = check(a1, nmax, min(4000, a1 * 40 + 200))
        worst.append((o["maxmu_over_a1rad"], a1, o))
        if o["bad_2.1"] or o["bad_4.2"] or o["bad_5.2_concl"]:
            print("VIOLATION", a1, o["bad_2.1"], o["bad_4.2"], o["bad_5.2_concl"])
    print("引理2.1 / 4.2 / 5.2结论: 无违例 (除下面列出的)")
    print("引理5.2 不等式 mu*p^(e-1)<a1 的反例 (mu>=a1):")
    cnt = 0
    for _, a1, o in worst:
        for x in o["bad_5.2_ineq"]:
            if cnt < 8:
                print(f"   a1={a1} mu={x[0]} p={x[1]} e={x[2]} mu*p^(e-1)={x[3]} >= a1={x[4]}")
            cnt += 1
    print(f"   共计 {cnt} 个 a1 出现该不等式失效")
    print("max mu/(a1*rad(a1)) =", max(w[0] for w in worst))
    print("max mu/(2a1) =", max(w[2]["maxmu_over_2a1"] for w in worst))
    print("max t/(2a1^2) =", max(w[2]["maxt_over_2a1sq"] for w in worst))
    print()
    for a1 in [2, 15, 35, 187, 385, 15015]:
        L, T, ok, ok2, head = period_check(a1, 200 if a1 > 1000 else 400)
        print(f"a1={a1}: L={L} T={T} 周期集合核对={ok}  a_(n+T)=a_n+L 全 n 核对={ok2} head={head}")

main()
