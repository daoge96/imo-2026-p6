import sys
sys.path.insert(0, r"D:\OneDrive\Desktop\dsh\imo-p6")
import verify as V

a1 = 15
res = V.stabilize(a1, 1024, nterms_cap=4000, stable_S=300)
terms = res["terms"]
inA = V.in_Ainf_factory(terms)
B = V.minimal_elements(a1, terms, 20000)
print("B", B)
base = terms[-1]
bad = []
for k in range(base, base + 98):
    marked = any(k % b == 0 for b in B)
    real = inA(k)
    if marked != real:
        bad.append((k, real, marked, V.factorize(k)))
print("mismatches:", len(bad))
for x in bad[:15]:
    print(" ", x)
# 扩展扫描上界，看是否漏掉 >20000 的极小元
B2 = V.minimal_elements(a1, terms, 60000)
print("B(upto 60000)", B2)
