import json, sys
p = r"D:\OneDrive\Desktop\dsh\imo-p6\logs\quick-summary.json"
d = json.load(open(p, encoding="utf-8"))
print("keys:", list(d.keys()))
rows = d.get("rows", [])
print("n rows:", len(rows))
# 例子表：结构化值 + 若干 a_1
want = [2, 3, 4, 6, 15, 18, 35, 105, 210, 385, 1001, 1155, 2310, 3003, 15015, 4096, 59049,
        78125, 177147, 55901, 43701]
print("%-9s %-5s %-6s %-8s %-8s %-6s %-7s" % ("a1", "N0", "kill", "T", "L", "|FME|", "L/T"))
for r in rows:
    if r["a1"] in want:
        print("%-9d %-5d %-6d %-8d %-8d %-6d %-7.2f" %
              (r["a1"], r["N0"], r["nkill"], r["T"], r["L"], r["FME_count"], r["L_over_T"]))
tl = d.get("tcl", [])
print("\nTCL rows:", len(tl), " max N*:", max((r["Nstar"] or 0) for r in tl),
      " a1@max:", max(tl, key=lambda r: r["Nstar"] or 0)["a1"])
print("N*>2a1^2:", [r["a1"] for r in tl if r.get("Nstar_le_2a1sq") is False])
print("range_insufficient:", [r["a1"] for r in tl if r["range_insufficient"]][:10])
sh = d.get("shadow", [])
print("shadow ex:", [(s["a1"], s["ex_nonempty"]["N"], s["ex_nonempty"]["m"]) for s in sh[:5]])
tr = d.get("trans", [])
print("trans last stage max:", max((t["last_kill_stage"] or 0) for t in tr),
      "count example:", tr[0]["count_kill_stages"])
print("warm:", d.get("warm_bad"), d.get("warm_literal_bad"), d.get("warm_identity_bad"))
