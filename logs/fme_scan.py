"""扫描：持久极小元(候选 A_inf 极小元) 的最大值/最大素因子 相对 a1、maxD1 的比例。"""
import sys
sys.path.insert(0, r"D:\OneDrive\Desktop\dsh\imo-p6\logs")
from fme_exp2 import persistent, factor

def main():
    lo, hi, nmax = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    rows = []
    for a1 in range(lo, hi + 1):
        r, pers, newpers = persistent(a1, nmax)
        if not pers:
            continue
        mx = max(pers)
        mp = max(max(factor(b)) for b in pers)
        Pi = max(factor(a1))
        mxsupp = max(len(factor(b)) for b in pers)
        rows.append(dict(a1=a1, Pi=Pi, mx=mx, mp=mp, k=len(pers), mxsupp=mxsupp,
                         r1=mx / a1, r2=mx / (a1 * Pi), r3=mp / Pi, D1=sorted(factor(a1)),
                         pers=sorted(pers)[:8], late=len(newpers)))
    rows.sort(key=lambda d: -d["r2"])
    print("a1      Pi  maxpers      maxprime  |pers| maxsupp   mx/(a1*Pi)  mp/Pi  D1")
    for d in rows[:20]:
        print(f"{d['a1']:6d} {d['Pi']:4d} {d['mx']:10d} {d['mp']:9d} {d['k']:5d} {d['mxsupp']:6d} "
              f"{d['r2']:10.4f} {d['r3']:6.3f}  {d['D1']}  pers={d['pers']}")
    print()
    print("max of mx/(a1*Pi):", max(d['r2'] for d in rows), " at a1=",
          max(rows, key=lambda d: d['r2'])['a1'])
    print("max of mp/Pi:", max(d['r3'] for d in rows), " at a1=",
          max(rows, key=lambda d: d['r3'])['a1'])
    print("max |pers|:", max(d['k'] for d in rows), "max maxsupp:", max(d['mxsupp'] for d in rows))
    print("violations mx<=a1*Pi:", [d['a1'] for d in rows if d['mx'] > d['a1'] * d['Pi']][:20])
    print("total a1 scanned:", len(rows), " late-born persistent:",
          [(d['a1'], d['late']) for d in rows if d['late']][:20])

main()
