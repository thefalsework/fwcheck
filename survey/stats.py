"""Headline statistics over a survey jsonl (python survey/stats.py survey/results.jsonl)."""
import json
import re
import sys

rows = [json.loads(l) for l in open(sys.argv[1], encoding="utf-8-sig") if l.strip()]
ok = [r for r in rows if not r["error"]]


def f(r, c, s=None):
    return [x for x in r["findings"] if x["check"] == c and (s is None or x["status"] == s)]


has_ci = [r for r in ok if any(x["check"] == "ci" and x["status"] != "UNVERIFIABLE" for x in r["findings"])]
print("repos:", len(ok))
print("repos with any workflow:", len(has_ci), "; with none:", len(ok) - len(has_ci))
stale_ci = [r for r in ok if f(r, "ci", "STALE")]
print("repos whose latest build/verify workflow run failed:", len(stale_ci))


def streak(x):
    m = re.search(r"(\d+) consecutive", x["evidence"])
    return int(m.group(1)) if m else 0


long = [r for r in stale_ci if any(streak(x) >= 2 for x in f(r, "ci", "STALE"))]
print("  of which 2+ consecutive failures:", len(long))
nosucc = [r for r in stale_ci if any("no success in last 30" in x["evidence"] for x in f(r, "ci", "STALE"))]
print("  of which no success in the last 30 runs:", len(nosucc))
cmp = [r for r in ok if f(r, "comparator_config")]
print("repos naming a comparator config:", len(cmp))
cmp_ci = [r for r in cmp if any(x["check"] == "ci" and x["status"] == "OK" and re.search(r"comparator|kernel|verif|replay|check", x["claim"], re.I) for x in r["findings"])]
print("  with a passing comparator/kernel/verify-named workflow:", len(cmp_ci))
cmp_noci = [r for r in cmp if not any(x["check"] == "ci" and x["status"] != "UNVERIFIABLE" for x in r["findings"])]
print("  with no CI at all:", len(cmp_noci))
zero = [r for r in ok if any(x["check"] == "sorry_count" and x["claim"].startswith("0") for x in r["findings"])]
print("claim sorry_count 0:", len(zero), "; contradicted:", len([r for r in zero if f(r, "sorry_count", "MISMATCH")]))
print("axioms backed:", len([r for r in ok if f(r, "axioms", "OK")]),
      "; custom axioms not in status.axioms:", len([r for r in ok if f(r, "axioms", "MISMATCH")]),
      "; axioms not stated, custom present:", len([r for r in ok if f(r, "axioms", "INFO") and any("does not state" in x["evidence"] for x in f(r, "axioms", "INFO"))]))
nd = [r for r in ok if f(r, "native_decide")]
print("native_decide used:", len(nd), "; ofReduceBool listed:", len([r for r in nd if f(r, "native_decide", "OK")]))
rv = {}
for r in ok:
    k = (r["review_status"] or "(none)").strip().lower()
    k = "human/peer" if re.search(r"peer|human|expert", k) and not re.search(r"no human|no independent|not claimed|unrun|remain", k) else k
    rv[k if len(k) <= 30 else "(free text)"] = rv.get(k if len(k) <= 30 else "(free text)", 0) + 1
print("review.status:", sorted(rv.items(), key=lambda kv: -kv[1])[:8])
print()
print("top by stars:")
for r in sorted(ok, key=lambda r: -r["stars"])[:20]:
    ci = "no CI" if r in [x for x in ok if x not in has_ci] else ("CI failing" if r in stale_ci else "CI ok")
    print(f"{r['stars']:>5} {r['repo']:<44} {ci:<10} {r['verdict']}")
