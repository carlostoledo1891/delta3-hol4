#!/usr/bin/env python3
"""client.py — the Mac side of the remote judge (used by attempt.py --host). hol4/delta3/harness/pod · 2026-11-25

run_remote(): sends one attempt to the pod's runner and waits for its raw facts.
  1. job id <family>-<lemma>-<n>-<random>; job.json (lemma, deps, limits) and script.sml are copied with scp to
     /root/judge/inbox/<job>.part, renamed to inbox/<job> and marked READY (the runner only takes READY jobs);
  2. polls with ssh for outbox/<job>/DONE (every 5 s; ssh failures are retried; the wait is bounded by
     JUDGE_REMOTE_WAIT seconds, default 6 h, since up to 8 run at a time and the rest queue);
  3. copies outbox/<job>/ back into the attempt's local directory (result.json, info.json, logs).
check_pod(): the pod must be at the frozen state — base scripts with the frozen sha256, HOL at the pinned
commit, and the SAME judgelib.py as this Mac (sha256) — or the attempt is refused.
Nothing is decided here: attempt.py calls judgelib.decide on the returned facts.
"""
import os, sys, json, time, uuid, shutil, subprocess, hashlib

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
REMOTE = os.environ.get('JUDGE_ROOT_REMOTE', '/root/judge')
HOL_COMMIT = json.load(open(os.path.join(HERE, 'PIN.json')))['hol_commit']   # the one pin


def _opts(port):
    o = ['-o', 'BatchMode=yes', '-o', 'StrictHostKeyChecking=accept-new', '-o', 'ConnectTimeout=20',
         '-o', 'ServerAliveInterval=30']
    k = os.environ.get('JUDGE_SSH_KEY')
    if k:
        o += ['-i', k]
    return o


def ssh(user, host, port, cmd, timeout=120):
    return subprocess.run(['ssh', '-p', str(port)] + _opts(port) + ['%s@%s' % (user, host), cmd],
                          capture_output=True, text=True, timeout=timeout)


def scp_to(user, host, port, local, remote, timeout=300):
    return subprocess.run(['scp', '-q', '-r', '-P', str(port)] + _opts(port) + [local, '%s@%s:%s' % (user, host, remote)],
                          capture_output=True, text=True, timeout=timeout)


def scp_from(user, host, port, remote, local, timeout=300):
    return subprocess.run(['scp', '-q', '-r', '-P', str(port)] + _opts(port) + ['%s@%s:%s' % (user, host, remote), local],
                          capture_output=True, text=True, timeout=timeout)


def run_remote(host, port, user, work, text, lemma, deps, family, n, time_s, cpu_s, mem_kb, mode='prove'):
    job = '%s-%s-%d-%s' % (family, lemma, n, uuid.uuid4().hex[:8])
    stage = os.path.join(work, 'remote-job', job)
    os.makedirs(stage)
    open(os.path.join(stage, 'script.sml'), 'w', encoding='utf-8').write(text)
    json.dump(dict(lemma=lemma, deps=deps, mode=mode, time_s=time_s, cpu_s=cpu_s, mem_kb=mem_kb, family=family, attempt=n,
                   sent_utc=time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())), open(os.path.join(stage, 'job.json'), 'w'))
    for tries in range(5):
        r = scp_to(user, host, port, stage, '%s/inbox/%s.part' % (REMOTE, job))
        if r.returncode == 0:
            break
        time.sleep(10)
    else:
        raise RuntimeError('scp to the pod failed: ' + r.stderr[-300:])
    r = ssh(user, host, port, 'mv %s/inbox/%s.part %s/inbox/%s && touch %s/inbox/%s/READY' % (REMOTE, job, REMOTE, job, REMOTE, job))
    if r.returncode != 0:
        raise RuntimeError('could not queue the job on the pod: ' + r.stderr[-300:])
    deadline = time.time() + int(os.environ.get('JUDGE_REMOTE_WAIT', str(6 * 3600)))
    while True:
        try:
            r = ssh(user, host, port, 'test -f %s/outbox/%s/DONE && echo DONE' % (REMOTE, job), timeout=60)
            if 'DONE' in r.stdout:
                break
        except subprocess.TimeoutExpired:
            pass
        if time.time() > deadline:
            raise RuntimeError('the pod did not finish job %s in time' % job)
        time.sleep(5)
    back = os.path.join(work, 'remote-out')
    r = scp_from(user, host, port, '%s/outbox/%s' % (REMOTE, job), back)
    if r.returncode != 0:
        raise RuntimeError('could not fetch the result: ' + r.stderr[-300:])
    for f in os.listdir(back):
        src = os.path.join(back, f)
        if os.path.isdir(src):
            shutil.copytree(src, os.path.join(work, f), dirs_exist_ok=True)
        else:
            shutil.copy(src, os.path.join(work, f))
    if os.path.exists(os.path.join(work, 'error.txt')):
        raise RuntimeError('the runner failed on the job: ' + open(os.path.join(work, 'error.txt')).read()[-500:])
    res = json.load(open(os.path.join(work, 'result.json')))
    info = json.load(open(os.path.join(work, 'info.json')))
    info['job'] = job
    return res, info


def check_pod(info, frozen):
    """None when the pod is at the frozen state, else what differs"""
    for k, v in info.get('base_sources', {}).items():
        if frozen['public'].get(k) != v:
            return '%s on the pod has sha256 %s…, the freeze says %s…' % (k, v[:12], (frozen['public'].get(k) or 'nothing')[:12])
    missing = [k for k in frozen['public'] if k.startswith('base/') and k not in info.get('base_sources', {})]
    if missing:
        return 'the pod lacks ' + ', '.join(missing)
    if info.get('hol_commit') != HOL_COMMIT:
        return 'HOL on the pod is at %s, not the pinned %s' % (info.get('hol_commit'), HOL_COMMIT[:12])
    mine = hashlib.sha256(open(os.path.join(HERE, 'judgelib.py'), 'rb').read()).hexdigest()
    if info.get('judgelib_sha256') != mine:
        return 'the pod runs a different judgelib.py (%s…, here %s…)' % (str(info.get('judgelib_sha256'))[:12], mine[:12])
    return None
