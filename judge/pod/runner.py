#!/usr/bin/env python3
"""runner.py — the judge's remote runner on a Linux pod. hol4/delta3/harness/pod · 2026-11-25

  python3 runner.py serve [--slots 8]     the daemon: takes jobs from inbox/, at most <slots> at a time
  python3 runner.py stop                  asks the daemon to stop after the jobs it is running (STOP file)
  python3 runner.py status                queued / running / done, the isolation probe, the last log lines
  python3 runner.py selftest              no network and no writes outside the run directory, checked as a slot user

Layout (JUDGE_ROOT, default /root/judge; made by setup-pod.sh):
  judgelib.py runner.py jail   the judge's code (judgelib.py is byte-identical to the Mac's: the client checks)
  base/                        the base theories, built from the frozen scripts
  inbox/<job>/{job.json, script.sml, READY}   written by the Mac's client (pod/client.py) over scp
  running/<job>/  runs/<job>/  outbox/<job>/{result.json, info.json, holmake.log, judge.out, judge.log, DONE}
Every job runs in its own fresh directory runs/<job>, owned by one of the slot users judge0..judge<slots-1>
(mode 700, so a job cannot read or write another's), under jail (seccomp: no sockets but unix ones;
Landlock where the kernel has it: no writes outside the run directory and /tmp), in a new network
namespace too when the container allows one, with the wall/CPU/memory limits of judgelib.run_limited.
The decision is NOT taken here: the raw facts go back and the Mac's attempt.py decides (judgelib.decide).
"""
import os, sys, json, time, shutil, hashlib, threading, subprocess, socket, pwd, traceback

ROOT = os.environ.get('JUDGE_ROOT', '/root/judge')
sys.path.insert(0, ROOT)
HOLDIR = os.environ.get('HOLDIR') or (json.load(open(os.path.join(ROOT, 'PIN.json')))['hol_dir_pod'] if os.path.exists(os.path.join(ROOT, 'PIN.json')) else '/root/work/HOL')
JAIL = os.path.join(ROOT, 'jail')
BASE = os.path.join(ROOT, 'base')
D = {k: os.path.join(ROOT, k) for k in ('inbox', 'running', 'outbox', 'runs')}
LOG = os.path.join(ROOT, 'runner.log')
STOP = os.path.join(ROOT, 'STOP')
POLY = os.environ.get('POLY_PREFIX', '/root/work/polyml-install')


def log(msg):
    with open(LOG, 'a') as f:
        f.write('%s %s\n' % (time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()), msg))


def sha(p):
    return hashlib.sha256(open(p, 'rb').read()).hexdigest()


def netns_available():
    try:
        return subprocess.run(['unshare', '-n', 'true'], capture_output=True, timeout=20).returncode == 0
    except Exception:
        return False


def probe():
    ll = subprocess.run([JAIL, '--probe'], capture_output=True, text=True).stdout.strip()
    return dict(landlock=ll, netns=netns_available(), kernel=os.uname().release)


def info():
    import judgelib
    srcs = {('base/' + f): sha(os.path.join(BASE, f)) for f in sorted(os.listdir(BASE)) if f.endswith('Script.sml')}
    hol = subprocess.run(['git', '-C', HOLDIR, 'rev-parse', 'HEAD'], capture_output=True, text=True).stdout.strip()
    return dict(host=socket.gethostname(), hol_commit=hol, base_sources=srcs, judgelib_sha256=sha(os.path.join(ROOT, 'judgelib.py')),
                jail_c_sha256=sha(os.path.join(ROOT, 'jail.c')), runner_sha256=sha(os.path.join(ROOT, 'runner.py')),
                probe=PROBE, poly=subprocess.run(['poly', '-v'], capture_output=True, text=True,
                                                 env=dict(os.environ, PATH=os.path.join(POLY, 'bin') + ':' + os.environ['PATH'])).stdout.strip())


def slot_user(k):
    p = pwd.getpwnam('judge%d' % k)
    return p.pw_uid, p.pw_gid


def demote(uid, gid, netns):
    def f():
        if netns and hasattr(os, 'unshare'):
            os.unshare(os.CLONE_NEWNET)
        os.setgroups([]); os.setgid(gid); os.setuid(uid)
    return f


def run_job(job, slot):
    import judgelib
    src = os.path.join(D['running'], job)
    out = os.path.join(D['outbox'], job)
    try:
        j = json.load(open(os.path.join(src, 'job.json')))
        text = open(os.path.join(src, 'script.sml'), encoding='utf-8').read()
        work = os.path.join(D['runs'], job)
        shutil.rmtree(work, ignore_errors=True); os.makedirs(work)
        uid, gid = slot_user(slot)
        os.chown(work, uid, gid); os.chmod(work, 0o700)
        # files the build needs are written by root first, then handed to the slot user
        open(os.path.join(work, 'attemptScript.sml'), 'w', encoding='utf-8').write(text)
        os.makedirs(os.path.join(work, 'tmp'), exist_ok=True)
        for dp, dn, fn in os.walk(work):
            for x in dn + fn:
                os.chown(os.path.join(dp, x), uid, gid)
        wrap = [JAIL, work, '--', 'env', 'PATH=%s:%s:/usr/bin:/bin' % (os.path.join(HOLDIR, 'bin'), os.path.join(POLY, 'bin')),
                'LD_LIBRARY_PATH=%s' % os.path.join(POLY, 'lib')]
        netns = PROBE['netns']
        iso = 'linux:jail(seccomp%s)+slot-user%s' % ('+landlock' if PROBE['landlock'] not in ('', 'landlock_abi=0') else '',
                                                    '+netns' if netns else '')
        # build_and_judge writes the Holmakefile and judge.sml as root: hand them over afterwards is too late,
        # so write them now with the same content it would write, then let it overwrite (root) — both readable.
        res = judgelib.build_and_judge(work, text, j['lemma'], j['deps'], BASE, HOLDIR, j['time_s'], j['cpu_s'], j['mem_kb'],
                                       'linux', wrap=wrap, preexec_extra=demote(uid, gid, netns), mode=j.get('mode', 'prove'))
        res['isolation'] = iso
        res['slot'] = slot
        os.makedirs(out, exist_ok=True)
        json.dump(res, open(os.path.join(out, 'result.json'), 'w'), indent=1)
        json.dump(info(), open(os.path.join(out, 'info.json'), 'w'), indent=1)
        for f in ('holmake.log', 'judge.out', 'judge.log'):
            if os.path.exists(os.path.join(work, f)):
                shutil.copy(os.path.join(work, f), out)
        tl = os.path.join(work, '.hol', 'logs', 'attemptTheory')
        if os.path.exists(tl):
            shutil.copy(tl, os.path.join(out, 'attemptTheory.log'))
        objs = os.path.join(work, '.hol', 'objs')          # the built theory, for the independent replay
        if os.path.isdir(objs):
            os.makedirs(os.path.join(out, 'theory'), exist_ok=True)
            for f in os.listdir(objs):
                if f.startswith('attemptTheory'):
                    shutil.copy(os.path.join(objs, f), os.path.join(out, 'theory', f))
        log('done %s slot %d outcome-facts build_rc=%s killed=%s' % (job, slot, res['build']['rc'], res['build']['killed']))
    except Exception:
        os.makedirs(out, exist_ok=True)
        open(os.path.join(out, 'error.txt'), 'w').write(traceback.format_exc())
        log('ERROR %s %s' % (job, traceback.format_exc().splitlines()[-1]))
    open(os.path.join(out, 'DONE'), 'w').write(time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()) + '\n')


def serve(slots):
    for d in D.values():
        os.makedirs(d, exist_ok=True)
    if os.path.exists(STOP):
        os.remove(STOP)
    log('serve: %d slots, probe %s' % (slots, PROBE))
    free = list(range(slots)); lock = threading.Lock(); threads = []
    def worker(job, slot):
        try:
            run_job(job, slot)
        finally:
            with lock:
                free.append(slot)
    while not os.path.exists(STOP):
        jobs = sorted(j for j in os.listdir(D['inbox']) if os.path.exists(os.path.join(D['inbox'], j, 'READY')))
        for job in jobs:
            with lock:
                if not free:
                    break
                slot = free.pop(0)
            os.rename(os.path.join(D['inbox'], job), os.path.join(D['running'], job))
            log('start %s slot %d' % (job, slot))
            t = threading.Thread(target=worker, args=(job, slot)); t.start(); threads.append(t)
        threads = [t for t in threads if t.is_alive()]
        time.sleep(2)
    log('serve: STOP seen, waiting for %d running job(s)' % len(threads))
    for t in threads:
        t.join()
    log('serve: stopped')


def selftest():
    """two checks as slot user judge0 under jail, no HOL: a TCP connect to a listener on 127.0.0.1 must
    fail, and a write outside the run directory must fail; the listener must see nothing."""
    uid, gid = slot_user(0)
    d = os.path.join(D['runs'], 'selftest'); shutil.rmtree(d, ignore_errors=True); os.makedirs(d); os.chown(d, uid, gid)
    srv = socket.socket(); srv.bind(('127.0.0.1', 0)); srv.listen(5); srv.settimeout(3); port = srv.getsockname()[1]
    code = ("import socket,sys\n"
            "try:\n socket.create_connection(('127.0.0.1',%d),timeout=3); print('CONNECTED')\n"
            "except Exception as e: print('DENIED connect', e)\n"
            "for p in ['%s/ESCAPE-1', '/tmp/../root/judge/ESCAPE-2', '%s/x']:\n"
            " try:\n  open(p,'w').write('x'); print('WROTE', p)\n except Exception as e: print('DENIED write', p, e)\n") % (
        port, ROOT, BASE)
    p = subprocess.run([JAIL, d, '--', 'python3', '-c', code], capture_output=True, text=True, preexec_fn=demote(uid, gid, PROBE['netns']))
    seen = 0
    try:
        c, _ = srv.accept(); seen = 1; c.close()
    except OSError:
        pass
    ok = 'CONNECTED' not in p.stdout and 'WROTE' not in p.stdout and seen == 0 and p.stdout.count('DENIED') == 4
    print(p.stdout + p.stderr)
    print('SELFTEST %s (listener saw %d connection(s); probe %s)' % ('PASS' if ok else 'FAIL', seen, PROBE))
    return 0 if ok else 1


PROBE = None
if __name__ == '__main__':
    cmd = sys.argv[1] if len(sys.argv) > 1 else 'status'
    if cmd == 'stop':
        open(STOP, 'w').write('stop\n'); print('STOP written; serve exits after its running jobs'); sys.exit(0)
    PROBE = probe()
    if cmd == 'serve':
        slots = int(sys.argv[sys.argv.index('--slots') + 1]) if '--slots' in sys.argv else 8
        serve(slots)
    elif cmd == 'status':
        q = [j for j in os.listdir(D['inbox'])] if os.path.isdir(D['inbox']) else []
        r = os.listdir(D['running']) if os.path.isdir(D['running']) else []
        o = [j for j in os.listdir(D['outbox']) if os.path.exists(os.path.join(D['outbox'], j, 'DONE'))] if os.path.isdir(D['outbox']) else []
        print(json.dumps(dict(queued=len(q), running_or_finished=len(r), done=len(o), probe=PROBE, stop_requested=os.path.exists(STOP))))
        if os.path.exists(LOG):
            print(''.join(open(LOG).readlines()[-10:]))
    elif cmd == 'selftest':
        sys.exit(selftest())
    elif cmd == 'info':
        print(json.dumps(info(), indent=1))
    else:
        sys.exit(__doc__)
