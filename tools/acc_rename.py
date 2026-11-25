#!/usr/bin/env python3
# tools/acc_rename.py <SOURCES.tsv> <repo root> <out dir> — writes acc_<id>Script.sml for every proof the
# assembly uses (proofs/accepted/, proofs/cleanroom/, proofs/builder/): the script with its one line "Theory attempt" renamed "Theory acc_<id>", nothing else.
# Refuses unless the source and the renamed file have the sha256 SOURCES.tsv records.
import csv, hashlib, os, re, sys
src, root, out = sys.argv[1], sys.argv[2], sys.argv[3]
rows = [l for l in open(src, encoding='utf-8') if not l.startswith('#')]
n = 0
for r in csv.DictReader(rows, delimiter='\t'):
    s, source = r['statement'], r['source']
    if source.endswith('S149-builder.sml'):
        path = os.path.join(root, 'proofs', 'builder', 'S149-builder.sml')
    elif source.startswith('cleanroom/'):
        path = os.path.join(root, 'proofs', 'cleanroom', os.path.basename(source))
    else:
        path = os.path.join(root, 'proofs', 'accepted', source, 'script.sml')
    b = open(path, 'rb').read()
    if hashlib.sha256(b).hexdigest() != r['script_sha256']:
        sys.exit('acc_rename: %s differs from the script SOURCES.tsv records' % path)
    t = b.decode('utf-8')
    if len(re.findall(r'^Theory attempt\s*$', t, re.M)) != 1:
        sys.exit('acc_rename: %s has not exactly one "Theory attempt" line' % path)
    t2 = re.sub(r'^Theory attempt\s*$', 'Theory acc_%s' % s, t, count=1, flags=re.M)
    if hashlib.sha256(t2.encode('utf-8')).hexdigest() != r['theory_script_sha256']:
        sys.exit('acc_rename: the renamed %s differs from SOURCES.tsv' % s)
    open(os.path.join(out, 'acc_%sScript.sml' % s), 'w', encoding='utf-8').write(t2)
    n += 1
print(n, 'proof theories written to', out)
