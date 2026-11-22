#!/usr/bin/env python3
"""Per-family scoring breakdown from a bench.py run log.

Why: the corpus is not one population (roadmap 0.5c). `argv-tasks` is the
ARG-V real-world set and its result decides whether bug-finding headroom is
59 points (roadmap 0.7) or the main event.

Scoring, per SV-COMP: TRUE correct +2, FALSE correct +1, TRUE wrong -32,
FALSE wrong -16. A correct FALSE is reported here BOTH ways -- as bench.py
scores it, and as the competition would with an unconfirmed witness (0) --
because that gap is the whole of roadmap 0.5.
"""
import re, sys, pathlib, collections

log = pathlib.Path(sys.argv[1]).read_text(errors="ignore")
row = re.compile(r"^  ([+.!?])\s+(\S+\.yml)\s+(\S+)\s+(\S+)\s*$", re.M)

fam_stat = collections.defaultdict(lambda: collections.Counter())
for mark, task, prop, verdict in row.findall(log):
    parts = task.split('/')
    fam = parts[1] if len(parts) > 2 and parts[0] == "sv-comp" else parts[0]
    st = fam_stat[fam]
    st["runs"] += 1
    if mark == "+":
        if verdict == "TRUE":
            st["true_ok"] += 1
        elif verdict == "FALSE":
            st["false_ok"] += 1
        else:
            st["other_ok"] += 1
    elif mark == "!":
        st["flagged"] += 1
    else:
        st["unproven"] += 1

hdr = f"{'family':<30}{'runs':>6}{'T ok':>6}{'F ok':>6}{'unprv':>7}{'score':>8}{'comp':>7}{'solved%':>9}"
print(hdr); print("-" * len(hdr))
tot = collections.Counter()
for fam in sorted(fam_stat, key=lambda f: -fam_stat[f]["runs"]):
    st = fam_stat[fam]
    score = 2*st["true_ok"] + st["false_ok"]
    comp  = 2*st["true_ok"]           # FALSE uncollectible without a 1.0 witness
    solved = st["true_ok"] + st["false_ok"]
    pct = 100*solved/st["runs"] if st["runs"] else 0
    print(f"{fam:<30}{st['runs']:>6}{st['true_ok']:>6}{st['false_ok']:>6}"
          f"{st['unproven']:>7}{score:>8}{comp:>7}{pct:>8.0f}%")
    for k, v in st.items(): tot[k] += v
score = 2*tot["true_ok"] + tot["false_ok"]
print("-" * len(hdr))
print(f"{'TOTAL':<30}{tot['runs']:>6}{tot['true_ok']:>6}{tot['false_ok']:>6}"
      f"{tot['unproven']:>7}{score:>8}{2*tot['true_ok']:>7}"
      f"{100*(tot['true_ok']+tot['false_ok'])/max(tot['runs'],1):>8.0f}%")
print()
print(f"'score'  = as bench.py reports it (correct FALSE = +1)")
print(f"'comp'   = what SV-COMP would award today (correct FALSE unconfirmed = 0)")
print(f"uncollectible: {tot['false_ok']} points")
if tot["flagged"]:
    print(f"\n!! {tot['flagged']} flagged row(s) -- inspect before believing any of this")
