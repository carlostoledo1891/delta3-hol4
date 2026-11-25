#!/usr/bin/env python3
"""tools/redact.py — the one redaction applied to the files of this repository that came from the private working
copy (cert-machine/hol4/delta3). Deterministic: the same input gives the same output, byte for byte, so anyone who
holds an original can rebuild the redacted copy and compare it, and the original's sha256 (kept beside each
redacted file as <file>.original.sha256) still matches the seals that name it.

  python3 tools/redact.py <original> <redacted>        writes the redacted copy, prints the counts as JSON
  python3 tools/redact.py --check <file>               exit 1 if anything the rules remove is still in <file>

What it removes, nothing else (rules applied in this order):
  host      a public IPv4 address, with or without :port (the judge pod's ssh endpoint) -> <judge-pod>
            (loopback and private ranges such as 127.0.0.1, which the sandbox controls use, are kept)
  path      /Users/<name>/Projects/cert-machine/...                                    -> <cert-machine>/...
            any other /Users/<name>/...                                                -> ~/...
            /private/tmp/claude-<uid>/...  (an agent session's scratch folder)         -> <tmp>
  private   the two private working folders' names (notes/<…>/, outreach/<…>/)         -> <private-notes>/, <private>/
  session   a session id of the agent tools (8-4-4-4-12 hexadecimal)                    -> <session>
  aside     in the work log only: the sentences about the operator's own plans ("the submission", an e-mail) and the
            folder names' remaining mentions, removed whole
"""
import json, re, sys
import os

IPV4 = re.compile(r'\b(\d{1,3})\.(\d{1,3})\.\d{1,3}\.\d{1,3}(?::\d{1,5})?\b')


def public(m):
    a, b = int(m.group(1)), int(m.group(2))
    return not (a in (0, 10, 127) or (a, b) == (192, 168) or (a, b) == (169, 254) or (a == 172 and 16 <= b <= 31))


RULES = [
    ('host', IPV4, lambda m: '<judge-pod>' if public(m) else m.group(0)),
    ('path', re.compile(r'/Users/[^/\s"\'`]+/Projects/cert-machine/'), '<cert-machine>/'),
    ('path', re.compile(r'/Users/[^/\s"\'`]+/'), '~/'),
    ('path', re.compile(r'/private/tmp/claude-\d+/[^\s"\'`)]*'), '<tmp>'),
    ('private', re.compile(r'notes/[a-z0-9]+-hol4-2026-11-24(/?)'), r'<private-notes>\1'),
    ('private', re.compile(r'outreach/[a-z0-9]+-2026-11(/?)'), r'<private>\1'),
    ('session', re.compile(r'\b[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}\b'), '<session>'),
]
# the work log's asides: a sentence (up to ". " or the end of the line) that mentions one of these is removed
# one private word (a name that stays out of this repository) is read from the environment, not written here:
# REDACT_WORD=<word> python3 tools/redact.py ... reproduces the published files byte for byte from the originals
_W = os.environ.get('REDACT_WORD', '').strip()
_WRX = (r'|\b' + re.escape(_W) + r'\b') if _W else ''
ASIDE = re.compile(r'(?i)\be-?mail\b|\bthe submission\b' + _WRX)
LEFT = re.compile(r'(?i)/Users/|/private/tmp/claude-' + _WRX)
LEFT_LOG = re.compile(LEFT.pattern + r'|(?i:\be-?mail\b|\bthe submission\b)')


def redact(text, worklog=False):
    counts = {}
    for name, rx, rep in RULES:
        if name == 'host':
            n = sum(1 for m in rx.finditer(text) if public(m))
            text = rx.sub(rep, text)
        else:
            text, n = rx.subn(rep, text)
        counts[name] = counts.get(name, 0) + n
    if worklog:
        out, n = [], 0
        for line in text.split('\n'):
            if ASIDE.search(line):
                parts = re.split(r'(?<=\.)\s+', line)
                keep = [p for p in parts if not ASIDE.search(p)]
                n += len(parts) - len(keep)
                line = ' '.join(keep)
                if not line.strip() or line.strip() in ('-', '*'):
                    continue
            out.append(line)
        text = '\n'.join(out)
        counts['aside'] = n
    return text, counts


def left(text, worklog=False):
    found = set(m.group(0) for m in (LEFT_LOG if worklog else LEFT).finditer(text))
    return sorted(found | set(m.group(0) for m in IPV4.finditer(text) if public(m)))


if __name__ == '__main__':
    if sys.argv[1] == '--check':
        bad = left(open(sys.argv[2], encoding='utf-8').read(), sys.argv[2].endswith('WORKLOG.md'))
        print(json.dumps(bad)); sys.exit(1 if bad else 0)
    src, dst = sys.argv[1], sys.argv[2]
    text = open(src, encoding='utf-8').read()
    wl = src.endswith('WORKLOG.md')
    red, counts = redact(text, worklog=wl)
    if left(red, wl):
        sys.exit('redact: still present after the rules: %s' % left(red, wl))
    open(dst, 'w', encoding='utf-8').write(red)
    print(json.dumps(counts, sort_keys=True))
