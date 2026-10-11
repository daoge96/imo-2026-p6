"""逐步 trace：哪个新生元素最终活下来(immortal)，哪个死掉；死亡的击杀者结构。"""
import sys
sys.path.insert(0, r"D:\OneDrive\Desktop\dsh\imo-p6\logs")
from fme_exp2 import build, factor, min_elems

def trace(a1, nmax, upto=25):
    r = build(a1, nmax)
    pers = set(r["hist"][nmax // 2]) & set(r["hist"][nmax])
    print("#" * 78)
    print(f"a1={a1}  D1={sorted(factor(a1))}  immortal set = {sorted(pers)}")
    # reconstruct stepwise info
    seq = r["seq"]
    birth_by_step = {}
    for st, child, parent, p in r["births"]:
        birth_by_step.setdefault(st, []).append((child, parent, p))
    death_by_step = {}
    for st, b in r["deaths"]:
        death_by_step.setdefault(st, []).append(b)
    for st in range(1, upto + 1):
        an = seq[st - 1]
        D = sorted(factor(an))
        bs = birth_by_step.get(st, [])
        ds = death_by_step.get(st, [])
        mark = lambda x: "IMMORTAL" if x in pers else "doomed"
        if bs or ds:
            print(f"step {st}: a={an} D={D}")
            for b in ds:
                print(f"    DEATH {b} supp={sorted(factor(b))} [{mark(b)}]")
            for child, parent, p in bs:
                print(f"    BIRTH {child} = {parent}*{p} supp={sorted(factor(child))} [{mark(child)}]")

def killstruct(a1, nmax):
    """for doomed elements: support size histogram; killer support"""
    r = build(a1, nmax)
    pers = set(r["hist"][nmax // 2]) & set(r["hist"][nmax])
    seq = r["seq"]
    print(f"--- a1={a1}: doomed元素支撑大小分布 / 击杀者大小 ---")
    hist = {}
    for st, b in r["deaths"]:
        s = len(factor(b))
        hist[s] = hist.get(s, 0) + 1
    print("   doomed support-size histogram:", dict(sorted(hist.items())))
    print("   immortal support sizes:", sorted({len(factor(b)) for b in pers}))
    print("   immortal min-prime values:", sorted({min(factor(b)) for b in pers}))
    print("   D1 =", sorted(factor(a1)))

for a1 in [int(x) for x in (sys.argv[1:] or ["15", "35", "187", "385", "15015"])]:
    trace(a1, 1200, upto=14)
    killstruct(a1, 1200)
