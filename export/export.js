#!/usr/bin/env node
/* export.js — writes the data file one slab certificate needs for the HOL4 check.
   hol4/delta3 · cert-machine · Day 1 (2026-11-24)

     DELTA3_ROOT=<repo> node export.js <cert.json> <out.dat> [--forge <name>]

   What goes into the .dat file, and what force each part has:

   CERTIFICATE  grid, lo, hi, B, eps, claim, theta, forms — the file's own numbers,
                numerator and denominator exactly as the JSON string gives them.
   MODEL        per cell (a_i, b_i), the full pairs (i, j, s_i s_j W_i W_j) and the cut
                pairs (i, j, s_i s_j, W_i W_j, 4U²·A_in), taken from the JavaScript
                verifier's own gridData (instruments/delta3/verify.js + model.js).
                On Day 1 these are DATA to the HOL4 check; deriving them inside HOL4
                from φ* is step 1 of the plan's Days 2–3.
   WITNESS      D (a common denominator), T, the weights d_i, the integer factor Lw.
                Untrusted hints: a wrong witness can only make the HOL4 check say F.

   The script also runs a BigInt MIRROR of the HOL4 function (same terms, same scaling,
   same weighted diagonal-dominance test) so the expected verdict is known before HOL4
   is asked, and prints its time. The mirror is not evidence; the kernel theorem is.

   --forge claim     claim raised by 2^-100                       (battery.js: PLANTED claim)
   --forge negmu     extra form yy[0,1] with multiplier -2^-100    (battery.js: PLANTED negative multiplier)
   --forge bound     B raised by 1/1000, claim recomputed          (battery.js: slab bound raised by 1e-3)
   In every forged export the WITNESS is the one found for the genuine certificate.

   MIT licensed. Part of cert-machine. */
'use strict';
const fs = require('fs');
const path = require('path');
const ROOT = process.env.DELTA3_ROOT || path.resolve(__dirname, '..', '..');
const Q = require(path.join(ROOT, 'instruments/interval/rational.js'));
const V = require(path.join(ROOT, 'instruments/delta3/verify.js'));
const { cholesky } = require(path.join(ROOT, 'instruments/delta3/psd.js'));

const U = 1096n, U2 = U * U;
const KIND = { yy: 0, '11': 1, y1: 2, yd: 3, '11d': 4, y: 5, '1': 6, mlo: 7, mhi: 8, mm: 9, mlo_y: 10, mlo_1: 11, mhi_y: 12, mhi_1: 13, tri: 14 };
const babs = x => (x < 0n ? -x : x);
const gcd = (a, b) => { a = babs(a); b = babs(b); while (b) { const t = a % b; a = b; b = t; } return a; };
const lcm = (a, b) => a / gcd(a, b) * b;
/* "p/q" or "p" exactly as written: no normalisation */
function raw(s) {
  if (typeof s !== 'string' || !/^-?\d+(\/\d+)?$/.test(s)) throw new Error('not a rational string: ' + s);
  const [a, b] = s.split('/');
  return [BigInt(a), b === undefined ? 1n : BigInt(b)];
}

function forge(cert, name) {
  const TINY = 1n << 100n;
  const c = JSON.parse(JSON.stringify(cert));
  const add = (s, p2, q2) => { const [p, q] = raw(s); return (p * q2 + p2 * q) + '/' + (q * q2); };
  if (name === 'claim') c.claim = add(c.claim, 1n, TINY);
  else if (name === 'negmu') c.forms.push(['yy', [0, 1], '-1/' + TINY]);
  else if (name === 'bound') {
    c.B = add(c.B, 1n, 1000n);
    const [bp, bq] = raw(c.B), [ep, eq] = raw(c.eps), n1 = BigInt(c.grid.length);
    c.claim = (bp * eq - ep * n1 * bq) + '/' + (bq * eq);
  } else throw new Error('unknown forgery ' + name);
  return c;
}

/* the rows the HOL4 function reads */
function rows(cert) {
  const gd = V.gridData(cert.grid);                      /* the JS verifier's model data */
  const n = gd.n;
  const W = gd.cells.map(c => BigInt(c.q - c.p));
  const ab = gd.cells.map(c => [c.a.n, c.a.d, c.b.n, c.b.d]);
  const full = gd.full.map(f => [BigInt(f.i), BigInt(f.j), BigInt(gd.cells[f.i].s * gd.cells[f.j].s) * W[f.i] * W[f.j]]);
  const cut = gd.cut.map(c => {
    const a4 = Q.mul(c.Ain, Q.R(4n * U2, 1n));
    if (a4.d !== 1n) throw new Error('cut area off the lattice');
    return [BigInt(c.i), BigInt(c.j), BigInt(c.sgn), W[c.i] * W[c.j], a4.n];
  });
  const theta = cert.theta.map(raw);
  const forms = cert.forms.map(f => {
    const [kind, idx, mu] = f;
    if (!(kind in KIND)) throw new Error('unknown kind ' + kind);
    const [mp, mq] = raw(mu);
    let i = 0, j = 0, k = 0, s = [1, 1, 1];
    if (kind === 'tri') { [i, j, k] = idx; s = idx[3]; }
    else if (Array.isArray(idx)) { [i, j] = idx; }
    else if (idx !== null) i = idx;
    return [KIND[kind], i, j, k, s[0], s[1], s[2], mp, mq].map(BigInt);
  });
  const sc = ['lo', 'hi', 'B', 'eps', 'claim'].map(k => raw(cert[k]));
  return { n, W, grid: cert.grid.map(BigInt), ab, full, cut, theta, forms, lo: sc[0], hi: sc[1], B: sc[2], eps: sc[3], claim: sc[4] };
}

/* the terms of p = L_theta - B - sum mu_f f, as [tag, i, j, p, q]:
   tag 0: 1   1: y_i   2: y_i y_j   3: mh   4: mh y_i   5: mh^2,  with mh = sum W_k y_k = U m */
function terms(R) {
  const out = []; let bad = null;
  const t = (tag, i, j, p, q) => out.push([tag, Number(i), Number(j), p, q]);
  R.ab.forEach(([ap, aq, bp, bq], i) => { t(1, i, 0, ap, aq); t(2, i, i, bp, bq); });
  for (const [i, j, c] of R.full) t(2, i, j, c, U2);
  if (R.cut.length !== R.theta.length) bad = 'theta length';
  R.cut.forEach(([i, j, sg, ww, ain], x) => {
    if (!R.theta[x]) return;
    const [tp, tq] = R.theta[x];
    if (tp < 0n || tq < tp) { bad = 'theta outside [0,1]'; return; }
    const om = tq - tp;
    if (sg === 1n) { t(2, i, j, om * ww, tq * U2); t(0, 0, 0, -(om * (4n * ww - ain)), tq * 4n * U2); }
    else { t(2, i, j, -(om * ww), tq * U2); t(0, 0, 0, -(tp * ain), tq * 4n * U2); }
  });
  t(0, 0, 0, -R.B[0], R.B[1]);
  const [lp, lq] = R.lo, [hp, hq] = R.hi;
  for (const [kind, i, j, k, s1, s2, s3, mp, mq] of R.forms) {
    if (mp < 0n) { bad = 'negative multiplier'; continue; }
    switch (Number(kind)) {
      case 0: t(2, i, j, -mp, mq); break;
      case 1: t(0, 0, 0, -mp, mq); t(1, i, 0, mp, mq); t(1, j, 0, mp, mq); t(2, i, j, -mp, mq); break;
      case 2: t(1, i, 0, -mp, mq); t(2, i, j, mp, mq); break;
      case 3: t(1, i, 0, -mp, mq); t(2, i, i, mp, mq); break;
      case 4: t(0, 0, 0, -mp, mq); t(1, i, 0, 2n * mp, mq); t(2, i, i, -mp, mq); break;
      case 5: t(1, i, 0, -mp, mq); break;
      case 6: t(0, 0, 0, -mp, mq); t(1, i, 0, mp, mq); break;
      case 7: t(3, 0, 0, -mp, mq * U); t(0, 0, 0, mp * lp, mq * lq); break;
      case 8: t(0, 0, 0, -(mp * hp), mq * hq); t(3, 0, 0, mp, mq * U); break;
      case 9: t(5, 0, 0, mp, mq * U2); t(3, 0, 0, -(mp * lp), mq * lq * U); t(3, 0, 0, -(mp * hp), mq * hq * U); t(0, 0, 0, mp * lp * hp, mq * lq * hq); break;
      case 10: t(4, i, 0, -mp, mq * U); t(1, i, 0, mp * lp, mq * lq); break;
      case 11: t(3, 0, 0, -mp, mq * U); t(0, 0, 0, mp * lp, mq * lq); t(4, i, 0, mp, mq * U); t(1, i, 0, -(mp * lp), mq * lq); break;
      case 12: t(1, i, 0, -(mp * hp), mq * hq); t(4, i, 0, mp, mq * U); break;
      case 13: t(0, 0, 0, -(mp * hp), mq * hq); t(1, i, 0, mp * hp, mq * hq); t(3, 0, 0, mp, mq * U); t(4, i, 0, -mp, mq * U); break;
      case 14: {
        if (i === j || j === k || i === k || s1 * s2 * s3 !== 1n) { bad = 'tri'; break; }
        t(0, 0, 0, -mp, mq);
        for (const [s, a, b] of [[s1, i, j], [s2, j, k], [s3, i, k]]) { const c = s * mp; t(0, 0, 0, -c, mq); t(1, a, 0, 2n * c, mq); t(1, b, 0, 2n * c, mq); t(2, a, b, -4n * c, mq); }
        break;
      }
      default: bad = 'kind';
    }
  }
  return { out, bad };
}

/* the integer matrix M = 2D(S + eps I), from the terms scaled by D */
function matrix(R, T, D) {
  const n = R.n;
  let ok = T.bad === null, k = 0n, mL = 0n, mM = 0n;
  const g = new Array(n).fill(0n), mY = new Array(n).fill(0n);
  const C = Array.from({ length: n }, () => new Array(n).fill(0n));
  for (const [tag, i, j, p, q] of T.out) {
    if (q === 0n || D % q !== 0n || !(i < n) || !(j < n)) { ok = false; continue; }
    const v = p * (D / q);
    if (tag === 0) k += v; else if (tag === 1) g[i] += v; else if (tag === 2) C[i][j] += v;
    else if (tag === 3) mL += v; else if (tag === 4) mY[i] += v; else mM += v;
  }
  if (D % R.eps[1] !== 0n) ok = false;
  const e2 = 2n * R.eps[0] * (D / R.eps[1]);
  const W = R.W;
  const M = Array.from({ length: n + 1 }, () => new Array(n + 1).fill(0n));
  M[0][0] = 2n * k + e2;
  for (let i = 0; i < n; i++) M[0][i + 1] = M[i + 1][0] = g[i] + mL * W[i];
  for (let i = 0; i < n; i++) for (let j = 0; j < n; j++)
    M[i + 1][j + 1] = C[i][j] + C[j][i] + W[i] * mY[j] + W[j] * mY[i] + 2n * mM * W[i] * W[j] + (i === j ? e2 : 0n);
  return { ok, M };
}

/* weighted diagonal dominance of 4^T M - 2D Lw Lw^T */
function dominated(M, D, Tw, d, Lw) {
  const N = M.length, c1 = 1n << BigInt(2 * Tw), c2 = 2n * D;
  for (let i = 0; i < N; i++) {
    let s = 0n;
    for (let j = 0; j < N; j++) {
      let dot = 0n; const a = Lw[i], b = Lw[j], m = Math.min(a.length, b.length);
      for (let x = 0; x < m; x++) dot += a[x] * b[x];
      const gij = c1 * M[i][j] - c2 * dot;
      s += d[j] * babs(gij) - (i === j ? 2n * d[j] * gij : 0n);
    }
    if (!(d[i] > 0n) || !(s <= 0n)) return false;
  }
  return true;
}

function findWitness(M, D) {
  const N = M.length;
  const A = M.map(r => r.map(x => Q.toDouble(Q.R(x, 2n * D))));
  const sh = A.map((r, i) => { if (!(r[i] > 0)) throw new Error('nonpositive diagonal at ' + i); return Math.round(Math.log2(r[i]) / 2); });
  const F = A.map((r, i) => r.map((x, j) => x * 2 ** (-(sh[i] + sh[j]))));
  const shmin = Math.min(...sh), shmax = Math.max(...sh);
  for (let k = 1; k <= 120; k++) {
    const ch = cholesky(F, 2 ** -k);
    if (ch.fail !== undefined) continue;
    const T0 = k + 60, S = 2 ** T0;
    const Lw = ch.L.map((row, i) => Array.from(row.slice(0, i + 1), x => BigInt(Math.round(x * S)) << BigInt(sh[i] - shmin)));
    const Tw = T0 - shmin;
    const d = sh.map(s => 1n << BigInt(shmax - s));
    if (dominated(M, D, Tw, d, Lw)) return { T: Tw, d, Lw, tauExp: k, shmin, shmax };
  }
  throw new Error('no witness found');
}

function main() {
  const args = process.argv.slice(2);
  const fi = args.indexOf('--forge');
  const forgeName = fi >= 0 ? args[fi + 1] : null;
  const [inFile, outFile] = args.filter((a, x) => !a.startsWith('--') && (fi < 0 || x !== fi + 1));
  const genuine = JSON.parse(fs.readFileSync(inFile, 'utf8'));
  /* witness from the genuine certificate */
  const Rg = rows(genuine), Tg = terms(Rg);
  let Dg = Rg.eps[1];
  for (const t of Tg.out) Dg = lcm(Dg, t[4]);
  const Mg = matrix(Rg, Tg, Dg);
  const wit = findWitness(Mg.M, Dg);
  /* the certificate to export */
  const cert = forgeName ? forge(genuine, forgeName) : genuine;
  const t0 = process.hrtime.bigint();
  const R = rows(cert), Tm = terms(R);
  let D = R.eps[1];
  for (const t of Tm.out) D = lcm(D, t[4]);
  const { ok, M } = matrix(R, Tm, D);
  const n = R.n;
  const [Bp, Bq] = R.B, [ep, eq] = R.eps, [cp, cq] = R.claim, [lp, lq] = R.lo, [hp, hq] = R.hi;
  const bound = Bp * eq - ep * BigInt(n + 1) * Bq;
  const scal = ep >= 0n && lp >= 0n && lp * hq < hp * lq && hp <= hq && cq > 0n && bound > 0n && cp * Bq * eq <= bound * cq;
  const dom = dominated(M, D, wit.T, wit.d, wit.Lw);
  const mirror = ok && scal && dom;
  const ms = Number(process.hrtime.bigint() - t0) / 1e6;
  const L = [];
  const sec = (name, rs) => { L.push('@' + name + ' ' + rs.length); for (const r of rs) L.push(r.join(' ')); };
  sec('grid', [R.grid]);
  sec('scal', [[lp, lq, hp, hq, Bp, Bq, ep, eq, cp, cq]]);
  sec('theta', R.theta);
  sec('forms', R.forms);
  sec('ab', R.ab);
  sec('cut', R.cut);
  sec('full', R.full);
  sec('wit', [[D, BigInt(wit.T)]]);
  sec('ds', [wit.d]);
  sec('L', wit.Lw);
  fs.writeFileSync(outFile, L.join('\n') + '\n');
  const bits = x => x.toString(2).length;
  let maxM = 0, maxL = 0;
  for (const r of M) for (const x of r) maxM = Math.max(maxM, bits(babs(x)));
  for (const r of wit.Lw) for (const x of r) maxL = Math.max(maxL, bits(babs(x)));
  console.log(JSON.stringify({
    cert: path.basename(inFile), forge: forgeName, out: path.basename(outFile), n, forms: R.forms.length, terms: Tm.out.length,
    full: R.full.length, cut: R.cut.length, Dbits: bits(D), Mbits: maxM, Lbits: maxL, T: wit.T, tauExp: wit.tauExp,
    weightSpread: wit.shmax - wit.shmin, mirror: { denominatorsOk: ok, scalarsOk: scal, dominated: dom, verdict: mirror, ms: Math.round(ms) },
    datBytes: fs.statSync(outFile).size,
  }));
}
main();
