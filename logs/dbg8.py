import sys, time
sys.path.insert(0, r"D:\OneDrive\Desktop\dsh\imo-p6")
import verify as V

for a1 in [30030, 46410, 45045, 60060, 255255, 510510, 720720]:
    t0 = time.time()
    gen = V.choice_gen(a1, 5000, stable_S=400)
    print("a1=%-8d terms=%-5d |Ls|=%-6d stable=%s N0=%-5d kill=%-5d %.2fs" %
          (a1, len(gen["terms"]), len(gen["Ls"]), gen["stable"], gen["last_kill"],
           gen["nkill"], time.time() - t0), flush=True)
