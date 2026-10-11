import sys, time
from math import gcd
sys.path.insert(0, r"D:\OneDrive\Desktop\dsh\imo-p6")
import verify as V

a1 = 30030
M = [frozenset(V.factorize(a1))]
Ls = V._prune(V._lcms_of(M))
terms = [a1]
t0 = time.time()
for step in range(1, 61):
    t = terms[-1]
    nxt = min(((t // L) + 1) * L for L in Ls)
    terms.append(nxt)
    D = frozenset(V.factorize(nxt))
    kill = any(not any(L % q == 0 for q in D) for L in Ls)
    M = V.minimal_sets(M + [D])
    ta = time.time()
    Ls = V._prune(V._lcms_of(M))
    print("step=%-3d a=%-8d D=%-22s |M|=%-3d |Ls|=%-6d kill=%-5s dM=%.3f dLs=%.3f"
          % (step, nxt, sorted(D), len(M), len(Ls), kill, 0, time.time() - ta), flush=True)
