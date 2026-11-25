#!/usr/bin/env python3
# tools/timed.py <tsv> <label> <log> <cmd...> — runs cmd under nice 10 with its output to <log>; appends
# "label, wall seconds, peak resident kB of the children, exit code" to <tsv>; exits with cmd's code.
import subprocess, sys, time, resource, platform
tsv, label, log, cmd = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4:]
t0 = time.time()
rc = subprocess.call(['nice', '-n', '10'] + cmd, stdout=open(log, 'w'), stderr=subprocess.STDOUT)
rss = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
if platform.system() == 'Darwin':
    rss //= 1024                                   # bytes on macOS, kB on Linux
open(tsv, 'a').write('%s\t%.2f\t%d\t%d\n' % (label, time.time() - t0, rss, rc))
sys.exit(rc)
