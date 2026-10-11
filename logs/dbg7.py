import sys, time
sys.path.insert(0, r"D:\OneDrive\Desktop\dsh\imo-p6")
import verify as V

for a1 in [210, 2310, 15015, 30030, 46410, 255255, 510510, 720720, 45045, 60060,
           999983, 1000003, 333667, 9699690 // 19]:
    t0 = time.time()
    g = V.choice_gen(a1, 5000, stable_S=400)
    print("a1=%-9d terms=%-5d |Ls|=%-6d stable=%s N0=%-4d kill=%-5d %.2fs" %
          (a1, len(g["terms"]), len(g["Ls"]), g["stable"], g["last_kill"], g["nkill"],
           time.time() - t0), flush=True)
