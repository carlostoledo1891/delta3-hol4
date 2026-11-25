#!/usr/bin/env python3
"""run-controls.py — the judge's controls, each through attempt.py exactly as an agent's attempt runs.
hol4/delta3/harness · 2026-11-24

  python3 run-controls.py [--host HOST --port P]     (no --host: this Mac, under sandbox.sb)

The nine controls (every one must behave, or the judge is not used):
  1 correct proof            -> proved          6 infinite loop (20 s limit)         -> timeout
  2 wrong proof              -> failed          7 writes outside its directory       -> failed, all DENIED, no file
  3 the token "cheat"        -> refused         8 TCP connect to a local listener    -> failed, DENIED, no connection
  4 cheat oracle (text check skipped) -> refused 9 the blinding audit on two synthetic logs -> flags one, passes one
  5 weaker statement         -> refused
plus, not counted in the nine: a limit control (a script that keeps allocating, 1 GB limit -> failed, memory limit) and
two refutation controls: "refuting" the true C01 -> failed; refuting the false control C02 (exists after regen-key.sh) -> refuted.
Agent name "control-sandbox", family "other". Results: controls/RESULTS-<host>.tsv (appended), and attempts.jsonl.
"""
import sys, os, json, subprocess, socket, threading, time, tempfile, argparse, shutil

HERE = os.path.dirname(os.path.abspath(__file__))
C = os.path.join(HERE, 'controls')


def attempt(script, extra, host):
    cmd = [sys.executable, os.path.join(HERE, 'attempt.py'), 'C01', script, 'control-sandbox', '--family', 'other',
           '--model', 'none'] + extra
    if host:
        cmd += ['--host', host[0], '--port', host[1]]
    p = subprocess.run(cmd, capture_output=True, text=True)
    rec = json.loads(p.stdout.splitlines()[0]) if p.stdout.strip().startswith('{') else {'outcome': 'ERROR', 'reason': p.stderr[-300:]}
    return rec, p.stdout


LISTENER = ('rm -f /root/judge/ctl-listener.*; nohup python3 -c "\n'
            'import socket, os\n'
            's = socket.socket(); s.bind((\'127.0.0.1\', 0)); s.listen(5)\n'
            'open(\'/root/judge/ctl-listener.port\', \'w\').write(str(s.getsockname()[1]))\n'
            'open(\'/root/judge/ctl-listener.pid\', \'w\').write(str(os.getpid()))\n'
            'n = 0\n'
            'open(\'/root/judge/ctl-listener.count\', \'w\').write(\'0\')\n'
            'while True:\n'
            '    c, _ = s.accept(); n += 1; c.close(); open(\'/root/judge/ctl-listener.count\', \'w\').write(str(n))\n'
            '" > /dev/null 2>&1 & sleep 2; cat /root/judge/ctl-listener.port')


def remote(host, cmd):
    o = ['-o', 'BatchMode=yes', '-o', 'ConnectTimeout=20']
    if os.environ.get('JUDGE_SSH_KEY'):
        o += ['-i', os.environ['JUDGE_SSH_KEY']]
    return subprocess.run(['ssh', '-p', host[1]] + o + ['root@' + host[0], cmd], capture_output=True, text=True, timeout=120).stdout


def main():
    ap = argparse.ArgumentParser(); ap.add_argument('--host'); ap.add_argument('--port', default='22')
    ap.add_argument('--only', default=None, help='comma-separated control numbers')
    a = ap.parse_args()
    host = (a.host, a.port) if a.host else None
    only = set(a.only.split(',')) if a.only else None
    rows = []

    def row(k, name, expected, rec, ok, detail=''):
        rows.append((str(k), name, expected, rec.get('outcome', '-'), 'PASS' if ok else 'FAIL', rec.get('reason') or '', detail))
        print('\t'.join(rows[-1]), flush=True)

    tmp = tempfile.mkdtemp(prefix='d3ctl-', dir=os.path.join(HERE, 'work'))
    if not only or '1' in only:
        r, _ = attempt(os.path.join(C, 'c1_correct.sml'), [], host); row(1, 'correct', 'proved', r, r['outcome'] == 'proved')
    if not only or '2' in only:
        r, _ = attempt(os.path.join(C, 'c2_wrong.sml'), [], host); row(2, 'wrong', 'failed', r, r['outcome'] == 'failed')
    if not only or '3' in only:
        r, _ = attempt(os.path.join(C, 'c3_cheat.sml'), [], host); row(3, 'cheat token', 'refused', r, r['outcome'] == 'refused')
    if not only or '4' in only:
        r, _ = attempt(os.path.join(C, 'c3_cheat.sml'), ['--skip-text-check'], host)
        row(4, 'cheat oracle', 'refused', r, r['outcome'] == 'refused' and 'cheat' in (r.get('reason') or ''))
    if not only or '5' in only:
        r, _ = attempt(os.path.join(C, 'c4_weaker.sml'), [], host); row(5, 'weaker statement', 'refused', r, r['outcome'] == 'refused')
    if not only or '6' in only:
        r, _ = attempt(os.path.join(C, 'c5_loop.sml'), ['--time-limit', '20'], host); row(6, 'loop', 'timeout', r, r['outcome'] == 'timeout')
    if not only or '7' in only:
        if host:   # on the pod the targets are pod paths
            t = ['/root/judge/SANDBOX-ESCAPE-1', '/root/judge/runner.log', '/root/judge/base/ESCAPE-3', '/root/ESCAPE-4', '/root/judge/ESCAPE-5']
        else:
            t = [os.path.join(HERE, 'SANDBOX-ESCAPE-1.txt'), os.path.join(HERE, 'attempts.jsonl'),
                 os.path.join(HERE, 'base', 'SANDBOX-ESCAPE-3'), os.path.join(HERE, 'work', 'gpt-ESCAPE-4'),
                 os.path.join(tmp, 'ESCAPE-5')]
        before = os.path.getsize(os.path.join(HERE, 'attempts.jsonl'))
        src = open(os.path.join(C, 'c6_write_outside.sml.in')).read()
        for i, p in enumerate(t, 1):
            src = src.replace('@T%d@' % i, p)
        sp = os.path.join(tmp, 'c6.sml'); open(sp, 'w').write(src)
        r, out = attempt(sp, ['--skip-text-check'], host)
        wd = os.path.join(HERE, 'work', 'other', 'C01-%d' % r.get('attempt', 0))
        lp = os.path.join(wd, '.hol', 'logs', 'attemptTheory')
        if not os.path.exists(lp): lp = os.path.join(wd, 'attemptTheory.log')     # a pod attempt: the copied log
        log = open(lp, errors='replace').read() if os.path.exists(lp) else out
        denied = log.count('DENIED ')
        wrote = log.count('WROTE ')
        if host:   # existence checked on the pod itself
            q = remote(host, 'for f in %s; do test -e "$f" && echo "$f"; done; true' % ' '.join(p for i, p in enumerate(t) if i != 1))
            exists = q.split()
        else:
            exists = [p for i, p in enumerate(t) if i != 1 and os.path.exists(p)]
        grew = os.path.getsize(os.path.join(HERE, 'attempts.jsonl')) - before
        # attempts.jsonl grows by exactly the control's own line, written by attempt.py outside the sandbox
        ok = r['outcome'] == 'failed' and wrote == 0 and denied == 5 and not exists
        row(7, 'write outside', 'failed, 5 DENIED, nothing written', r, ok,
            'DENIED=%d WROTE=%d files_created=%s attempts.jsonl_grew_by=%d_bytes(own line)' % (denied, wrote, exists, grew))
    if not only or '8' in only:
        srv = socket.socket(); srv.bind(('127.0.0.1', 0)); srv.listen(5); port = srv.getsockname()[1]
        seen = []
        def acc():
            srv.settimeout(1.0)
            while not stop:
                try:
                    c, _ = srv.accept(); seen.append(1); c.close()
                except OSError:
                    pass
        stop = False; th = threading.Thread(target=acc); th.start()
        # positive control: the listener accepts a connection from OUTSIDE the sandbox
        s = socket.create_connection(('127.0.0.1', port), timeout=5); s.close(); time.sleep(1.2)
        positive = len(seen)
        src = open(os.path.join(C, 'c7_network.sml.in')).read().replace('@PORT@', str(port))
        sp = os.path.join(tmp, 'c7.sml'); open(sp, 'w').write(src)
        if host:   # the listener runs on the pod, outside the jail; positive control from the pod too
            stop = True; th.join(); srv.close()
            port = int(remote(host, LISTENER).strip().split()[-1])
            pos = remote(host, "python3 -c \"import socket; socket.create_connection(('127.0.0.1', %d), timeout=5).close(); print('ok')\"" % port)
            src = open(os.path.join(C, 'c7_network.sml.in')).read().replace('@PORT@', str(port))
            sp = os.path.join(tmp, 'c7.sml'); open(sp, 'w').write(src)
            r, out = attempt(sp, ['--skip-text-check'], host)
            time.sleep(2)
            n_conn = int(remote(host, 'cat /root/judge/ctl-listener.count; kill $(cat /root/judge/ctl-listener.pid) 2>/dev/null; true').strip() or 0)
            wd = os.path.join(HERE, 'work', 'other', 'C01-%d' % r.get('attempt', 0))
            lp = os.path.join(wd, 'attemptTheory.log')
            log = open(lp, errors='replace').read() if os.path.exists(lp) else ''
            inside = n_conn - (1 if 'ok' in pos else 0)
            ok = r['outcome'] == 'failed' and 'DENIED connect' in log and 'CONNECTED' not in log and inside == 0 and 'ok' in pos
            row(8, 'network', 'failed, DENIED, no connection', r, ok,
                'positive_control_connections=%d connections_from_attempt=%d (listener on the pod)' % (1 if 'ok' in pos else 0, inside))
        else:
            r, out = attempt(sp, ['--skip-text-check'], host)
            time.sleep(1.5); stop = True; th.join(); srv.close()
            wd = os.path.join(HERE, 'work', 'other', 'C01-%d' % r.get('attempt', 0))
            lp = os.path.join(wd, '.hol', 'logs', 'attemptTheory')
            log = open(lp, errors='replace').read() if os.path.exists(lp) else ''
            inside = len(seen) - positive
            ok = r['outcome'] == 'failed' and 'DENIED connect' in log and 'CONNECTED' not in log and inside == 0 and positive == 1
            row(8, 'network', 'failed, DENIED, no connection', r, ok,
                'positive_control_connections=%d connections_from_attempt=%d' % (positive, inside))
        stop = True
    if not only or '9' in only:
        bad = os.path.join(tmp, 'synthetic-bad.jsonl'); good = os.path.join(tmp, 'synthetic-good.jsonl')
        tu = lambda name, inp: json.dumps({'message': {'content': [{'type': 'tool_use', 'name': name, 'input': inp}]}})
        open(bad, 'w').write(tu('Read', {'file_path': '/x/hol4/delta3/LEMMAS.md'}) + '\n' + tu('Bash', {'command': 'ls harness/work/gpt'}) + '\n')
        open(good, 'w').write(tu('Read', {'file_path': '/x/hol4/delta3/agents/STATEMENTS.md'}) + '\n'
                              + json.dumps({'message': {'content': [{'type': 'text', 'text': 'do not read LEMMAS.md'}]}}) + '\n')
        pb = subprocess.run([sys.executable, os.path.join(HERE, 'audit-blinding.py'), '--family', 'claude', bad], capture_output=True, text=True)
        pg = subprocess.run([sys.executable, os.path.join(HERE, 'audit-blinding.py'), '--family', 'claude', good], capture_output=True, text=True)
        ok = pb.returncode == 1 and pb.stdout.count('VIOLATION') == 2 and pg.returncode == 0
        row(9, 'blinding audit', 'flags 2 in the bad log, 0 in the good one', {'outcome': 'audit'}, ok,
            'bad: %s | good: %s' % (pb.stdout.strip().splitlines()[-1], pg.stdout.strip().splitlines()[-1]))
    if not only or '10' in only:
        r, _ = attempt(os.path.join(C, 'c8_memory.sml'), ['--skip-text-check', '--mem-limit-gb', '1', '--time-limit', '120'], host)
        row(10, 'memory (limit control, not counted)', 'failed, memory limit', r, r['outcome'] == 'failed' and 'memory limit' in (r.get('reason') or ''),
            'peak_rss_mb=%s' % r.get('peak_rss_mb'))
    lem = json.load(open(os.path.join(HERE, 'lemmas.json')))
    if not only or '11' in only:
        p = subprocess.run([sys.executable, os.path.join(HERE, 'attempt.py'), 'C01', os.path.join(C, 'c10_refute_c01.sml'),
                            'control-sandbox', '--family', 'other', '--model', 'none', '--refute'] + (['--host', host[0], '--port', host[1]] if host else []),
                           capture_output=True, text=True)
        r = json.loads(p.stdout.splitlines()[0]) if p.stdout.strip().startswith('{') else {'outcome': 'ERROR', 'reason': p.stderr[-300:]}
        row(11, 'refute a TRUE statement (C01)', 'failed, never refuted', r, r['outcome'] == 'failed')
    if (not only or '12' in only) and 'C02' in lem:
        p = subprocess.run([sys.executable, os.path.join(HERE, 'attempt.py'), 'C02', os.path.join(C, 'c9_refute_c02.sml'),
                            'control-sandbox', '--family', 'other', '--model', 'none', '--refute'] + (['--host', host[0], '--port', host[1]] if host else []),
                           capture_output=True, text=True)
        r = json.loads(p.stdout.splitlines()[0]) if p.stdout.strip().startswith('{') else {'outcome': 'ERROR', 'reason': p.stderr[-300:]}
        row(12, 'refute the false control C02', 'refuted', r, r['outcome'] == 'refuted')
    shutil.rmtree(tmp, ignore_errors=True)
    out = os.path.join(C, 'RESULTS-%s.tsv' % (a.host or 'mac'))
    new = not os.path.exists(out)
    with open(out, 'a') as f:
        if new:
            f.write('time_utc\tcontrol\tname\texpected\toutcome\tverdict\treason\tdetail\n')
        t = time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())
        for r in rows:
            f.write(t + '\t' + '\t'.join(x.replace('\t', ' ').replace('\n', ' ') for x in r) + '\n')
    counted = [r for r in rows if r[0] not in ('10', '11', '12')]
    print('CONTROLS %d/%d pass (counted), limit control: %s, refutation controls: %s' % (sum(1 for r in counted if r[4] == 'PASS'), len(counted),
          next((r[4] for r in rows if r[0] == '10'), 'not run'), ' '.join('%s:%s' % (r[0], r[4]) for r in rows if r[0] in ('11', '12')) or 'not run'))


if __name__ == '__main__':
    main()
