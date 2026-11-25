#!/usr/bin/env python3
# make-cover.py — UNTRUSTED converter: writes the cover inputs (d3/cover*.d3) from the regions the
# five .d3 data files already carry (the slab's lo, hi = the first four numbers of "@scal"; the
# inner certificate's region [0, rin], rin = the first two numbers of its "@scal").
# The three forged covers are the three cover forgeries of instruments/delta3/battery.js:
#   cover_red_gap      the slab [3/10, 2/5] missing           (battery: "slab [3/10, 2/5] missing")
#   cover_red_noinner  the inner certificate missing          (battery: "inner certificate missing")
#   cover_red_short    the last slab relabelled [2/5, 9/20]   (battery: "cover stops short of 1/2")
# A mistake here can only make an input wrong; the binary and the kernel then decide that input.
# Usage: python3 -I make-cover.py <hol4/delta3 directory> <output directory>
import os, sys

src, out = sys.argv[1], sys.argv[2]

def scal(path):
    with open(path) as f:
        lines = f.read().split("\n")
    for i, l in enumerate(lines):
        if l.startswith("@scal"):
            return [int(x) for x in lines[i + 1].split()]
    raise SystemExit("no @scal in " + path)

inner = scal(os.path.join(src, "day2", "inner.d3"))
regions = [("inner", (0, 1, inner[0], inner[1]))]
for nm in ["slabA", "slabB", "slabC", "slabD"]:
    s = scal(os.path.join(src, nm + ".d3"))
    regions.append((nm, tuple(s[0:4])))
# in order of the lower end
regions.sort(key=lambda r: r[1][0] / r[1][1])

def write(name, regs):
    p = os.path.join(out, name + ".d3")
    with open(p, "w") as f:
        f.write("@cover %d\n" % len(regs))
        for _, (a, b, c, d) in regs:
            f.write("%d %d %d %d\n" % (a, b, c, d))
    print(name, " ".join("%s=[%d/%d,%d/%d]" % ((n,) + r) for n, r in regs))

write("cover", regions)
write("cover_red_gap", [r for r in regions if r[0] != "slabB"])
write("cover_red_noinner", [r for r in regions if r[0] != "inner"])
write("cover_red_short", [(n, (2, 5, 9, 20)) if n == "slabD" else (n, r) for n, r in regions])
