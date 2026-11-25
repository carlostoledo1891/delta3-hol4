#!/usr/bin/env python3
# make-battery.py — UNTRUSTED converter: writes full .d3 files for the 37 certificate forgeries of
# battery.js as Astra's H1 run stored them (<private-notes>/astra-hol4-inner/work/data:
# cases.json + one partial file rNN.d3 per forgery), so that the FROZEN checker can be run on them in
# the HOL4 kernel and by the CakeML binary. Astra's generate.py applies a partial file to its base as:
#   grid, scal, wit : the section is replaced;
#   any other key   : rows = base[:left] + part + base[end:], with [left, end] = cases.json edits[key].
# This script does exactly that and writes the whole file. r24 (the malformed rational "2.7e-4" for B,
# refused by Astra's loader before the kernel) becomes slabC with B's two fields "2.7e-4" and "1" — what
# Astra's rat_fields makes of it — so that both loaders see the same malformed token.
# A mistake here can only make an input wrong; the kernel and the binary then decide that same input.
# Usage: python3 -I make-battery.py <astra work/data dir> <output dir>
import json, os, sys

data, out = sys.argv[1], sys.argv[2]
os.makedirs(out, exist_ok=True)

def read(path):
    secs, order, cur = {}, [], None
    with open(path) as f:
        for line in f.read().split("\n"):
            if line.startswith("@"):
                nm = line.split()[0][1:]
                cur = nm; order.append(nm); secs[nm] = []
            elif cur is not None and line.strip():
                secs[cur].append(line.strip())
    return order, secs

def write(path, order, secs):
    with open(path, "w") as f:
        for nm in order:
            f.write("@%s %d\n" % (nm, len(secs[nm])))
            for r in secs[nm]:
                f.write(r + "\n")

cases = json.load(open(os.path.join(data, "cases.json")))["cases"]
rows = []
for c in cases:
    if c["class"] == "green":
        continue
    cid, base = c["id"], c["base"]
    order, secs = read(os.path.join(data, base + ".d3"))
    secs = {k: list(v) for k, v in secs.items()}
    if c["class"] == "loader":
        raw = open(os.path.join(data, cid + ".raw")).read().split()[0]
        s = secs["scal"][0].split()
        s[4], s[5] = raw, "1"            # B = Bp/Bq is the third pair of "@scal"
        secs["scal"] = [" ".join(s)]
    else:
        porder, part = read(os.path.join(data, cid + ".d3"))
        for k in porder:
            if k in ("grid", "scal", "wit"):
                secs[k] = part[k]
            else:
                left, end = c["edits"][k]
                secs[k] = secs[k][:left] + part[k] + secs[k][end:]
    write(os.path.join(out, cid + ".d3"), order, secs)
    rows.append((cid, base, c["class"], c["name"]))
with open(os.path.join(out, "battery-cases.tsv"), "w") as f:
    f.write("id\tbase\tclass\tname\n")
    for r in rows:
        f.write("\t".join(r) + "\n")
print(len(rows), "files written to", out)
