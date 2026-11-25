#!/usr/bin/env node
/* export_inner.js — the data file for the INNER certificate, for inner_check (delta3_check2).
   hol4/delta3 · cert-machine · Day 2 (2026-11-24)

     DELTA3_ROOT=<repo> node export_inner.js <inner.json> <out.d3> [--forge kap|c0|radius]

   Same division of force as export.js: CERTIFICATE numbers as the file writes them; MODEL
   constants from the JavaScript verifier's gridData (still data, not derived in HOL4);
   WITNESS (D, T, weights, integer factor) untrusted, found by a float Cholesky and kept only
   if a BigInt mirror of the HOL4 test — STRICT weighted diagonal dominance — accepts it.

   --forge kap     kap := -2^-100                          (battery.js: PLANTED inner kap)
   --forge c0      c[0] := -(c[0] + 1)                     (battery.js: linear budget overspent)
   --forge radius  rin := 2/5                              (battery.js: inner radius doubled)
   A forged export keeps the genuine witness.   MIT licensed. Part of cert-machine. */
'use strict';
const fs = require('fs'), path = require('path');
const ROOT = process.env.DELTA3_ROOT || path.resolve(__dirname, '..', '..');
const Q = require(path.join(ROOT, 'instruments/interval/rational.js'));
const V = require(path.join(ROOT, 'instruments/delta3/verify.js'));
const { cholesky } = require(path.join(ROOT, 'instruments/delta3/psd.js'));
const U = 1096n, U2 = U * U;
const babs = x => (x < 0n ? -x : x);
const gcd = (a, b) => { a = babs(a); b = babs(b); while (b) { const t = a % b; a = b; b = t; } return a; };
const lcm = (a, b) => a / gcd(a, b) * b;
function raw(s) {
  if (typeof s !== 'string' || !/^-?\d+(\/\d+)?$/.test(s)) throw new Error('not a rational string: ' + s);
  const [a, b] = s.split('/'); return [BigInt(a), b === undefined ? 1n : BigInt(b)];
}
const key = k => k.split(',').map(x => BigInt(x));

function rows(cert) {
  const gd = V.gridData(cert.grid), n = gd.n;
  const W = gd.cells.map(c => BigInt(c.q - c.p));
  return {
    n, W, grid: cert.grid.map(BigInt),
    ab: gd.cells.map(c => [c.a.n, c.a.d, c.b.n, c.b.d]),
    full: gd.full.map(f => [BigInt(f.i), BigInt(f.j), BigInt(gd.cells[f.i].s * gd.cells[f.j].s) * W[f.i] * W[f.j]]),
    cut: gd.cut.map(c => { const a4 = Q.mul(c.Ain, Q.R(4n * U2, 1n)); return [BigInt(c.i), BigInt(c.j), BigInt(c.sgn), W[c.i] * W[c.j], a4.n]; }),
    rin: raw(cert.rin), kap: raw(cert.kap),
    lam: Object.entries(cert.lam).map(([k, v]) => [...key(k), ...raw(v)]),
    nu: cert.nu.map(raw), cc: cert.c.map(raw),
    nn: Object.entries(cert.N).map(([k, v]) => [...key(k), ...raw(v)]),
  };
}
/* terms [tag, i, j, p, q] exactly as inner_poly adds them */
function terms(R) {
  const out = []; let bad = null;
  const t = (tag, i, j, p, q) => out.push([tag, Number(i), Number(j), p, q]);
  const [rp, rq] = R.rin, [kp, kq] = R.kap;
  R.ab.forEach(([ap, aq, bp, bq], i) => { t(1, i, 0, ap, aq); t(2, i, i, bp, bq); });
  for (const [i, j, c] of R.full) t(2, i, j, c, U2);
  for (const [i, j, sg, ww] of R.cut) if (sg === -1n) t(2, i, j, -ww, U2);
  for (const [i, j, p, q] of R.lam) { if (p < 0n) bad = 'lam'; t(1, i, 0, -p, q); t(2, i, j, p, q); }
  R.nu.forEach(([p, q], j) => { if (p < 0n) bad = 'nu'; t(1, j, 0, -(p * rp), q * rq); t(4, j, 0, p, q * U); });
  if (kp < 0n) bad = 'kap';
  t(3, 0, 0, -(kp * rp), kq * rq * U); t(5, 0, 0, kp, kq * U2);
  for (const [i, j, p, q] of R.nn) { if (p < 0n || j < i) bad = 'N'; t(2, i, j, -(i === j ? p : 2n * p), q); }
  R.cc.forEach(([p, q], i) => { if (p < 0n) bad = 'c'; t(1, i, 0, -p, q); });
  return { out, bad };
}
function matrix(R, T, D) {
  const n = R.n; let ok = T.bad === null, k = 0n, mL = 0n, mM = 0n;
  const g = new Array(n).fill(0n), mY = new Array(n).fill(0n);
  const C = Array.from({ length: n }, () => new Array(n).fill(0n));
  for (const [tag, i, j, p, q] of T.out) {
    if (q === 0n || D % q !== 0n || !(i < n) || !(j < n)) { ok = false; continue; }
    const v = p * (D / q);
    if (tag === 0) k += v; else if (tag === 1) g[i] += v; else if (tag === 2) C[i][j] += v;
    else if (tag === 3) mL += v; else if (tag === 4) mY[i] += v; else mM += v;
  }
  const W = R.W;
  const lin0 = k === 0n && g.every((x, i) => x + mL * W[i] === 0n);
  const P = Array.from({ length: n }, (_, i) => Array.from({ length: n }, (_, j) =>
    C[i][j] + C[j][i] + W[i] * mY[j] + W[j] * mY[i] + 2n * mM * W[i] * W[j]));
  return { ok, lin0, P };
}
function strictlyDominated(M, D, Tw, d, Lw) {
  const N = M.length, c1 = 1n << BigInt(2 * Tw), c2 = 2n * D;
  for (let i = 0; i < N; i++) {
    let s = 0n;
    for (let j = 0; j < N; j++) {
      let dot = 0n; const a = Lw[i], b = Lw[j], m = Math.min(a.length, b.length);
      for (let x = 0; x < m; x++) dot += a[x] * b[x];
      const gij = c1 * M[i][j] - c2 * dot;
      s += d[j] * babs(gij) - (i === j ? 2n * d[j] * gij : 0n);
    }
    if (!(d[i] > 0n) || !(s < 0n)) return false;
  }
  return true;
}
function findWitness(M, D) {
  const A = M.map(r => r.map(x => Q.toDouble(Q.R(x, 2n * D))));
  const sh = A.map((r, i) => { if (!(r[i] > 0)) throw new Error('nonpositive diagonal at ' + i); return Math.round(Math.log2(r[i]) / 2); });
  const F = A.map((r, i) => r.map((x, j) => x * 2 ** (-(sh[i] + sh[j]))));
  const shmin = Math.min(...sh), shmax = Math.max(...sh);
  for (let k = 1; k <= 120; k++) {
    const ch = cholesky(F, 2 ** -k);
    if (ch.fail !== undefined) continue;
    const T0 = k + 60, S = 2 ** T0;
    const Lw = ch.L.map((row, i) => Array.from(row.slice(0, i + 1), x => BigInt(Math.round(x * S)) << BigInt(sh[i] - shmin)));
    const d = sh.map(s => 1n << BigInt(shmax - s));
    if (strictlyDominated(M, D, T0 - shmin, d, Lw)) return { T: T0 - shmin, d, Lw, tauExp: k };
  }
  throw new Error('no witness found');
}
function main() {
  const args = process.argv.slice(2), fi = args.indexOf('--forge');
  const forgeName = fi >= 0 ? args[fi + 1] : null;
  const [inFile, outFile] = args.filter((a, x) => !a.startsWith('--') && (fi < 0 || x !== fi + 1));
  const genuine = JSON.parse(fs.readFileSync(inFile, 'utf8'));
  const Rg = rows(genuine), Tg = terms(Rg);
  let Dg = 1n; for (const t of Tg.out) Dg = lcm(Dg, t[4]);
  const wit = findWitness(matrix(Rg, Tg, Dg).P, Dg);
  const cert = JSON.parse(JSON.stringify(genuine));
  if (forgeName === 'kap') cert.kap = '-1/' + (1n << 100n);
  else if (forgeName === 'c0') { const [p, q] = raw(cert.c[0]); cert.c[0] = (-(p + q)) + '/' + q; }
  else if (forgeName === 'radius') cert.rin = '2/5';
  else if (forgeName) throw new Error('unknown forgery ' + forgeName);
  const t0 = process.hrtime.bigint();
  const R = rows(cert), Tm = terms(R);
  let D = 1n; for (const t of Tm.out) D = lcm(D, t[4]);
  const { ok, lin0, P } = matrix(R, Tm, D);
  const [rp, rq] = R.rin;
  const scal = rq > 0n && rp > 0n && rp <= rq;
  const dom = strictlyDominated(P, D, wit.T, wit.d, wit.Lw);
  const ms = Number(process.hrtime.bigint() - t0) / 1e6;
  const L = [];
  const sec = (name, rs) => { L.push('@' + name + ' ' + rs.length); for (const r of rs) L.push(r.join(' ')); };
  sec('grid', [R.grid]); sec('scal', [[rp, rq, R.kap[0], R.kap[1]]]);
  sec('lam', R.lam); sec('nu', R.nu); sec('nn', R.nn); sec('cc', R.cc);
  sec('ab', R.ab); sec('cut', R.cut); sec('full', R.full);
  sec('wit', [[D, BigInt(wit.T)]]); sec('ds', [wit.d]); sec('L', wit.Lw);
  fs.writeFileSync(outFile, L.join('\n') + '\n');
  const bits = x => x.toString(2).length; let maxM = 0;
  for (const r of P) for (const x of r) maxM = Math.max(maxM, bits(babs(x)));
  console.log(JSON.stringify({ cert: path.basename(inFile), forge: forgeName, out: path.basename(outFile), n: R.n,
    lam: R.lam.length, nn: R.nn.length, terms: Tm.out.length, full: R.full.length, cut: R.cut.length, Dbits: bits(D), Mbits: maxM,
    T: wit.T, tauExp: wit.tauExp,
    mirror: { denominatorsAndSignsOk: ok, constantAndLinearZero: lin0, scalarsOk: scal, strictlyDominated: dom, verdict: ok && lin0 && scal && dom, ms: Math.round(ms) },
    datBytes: fs.statSync(outFile).size }));
}
main();
