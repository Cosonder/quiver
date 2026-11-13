// Run: node tests/lambda.test.js
// Tests for lambda-core.js (Canesin–Cao–Janssens, arXiv:2605.03925v2).
const assert = require('assert');
const L = require('../lambda-core.js');

const rnd = (n) => Math.floor(Math.random() * n);
const T = (M) => M[0].map((_, j) => M.map((r) => r[j]));

// ---- exact determinant / adjugate
{
  const M = [[2, 1, 0], [1, 3, 1], [0, 1, 4]];
  const r = L.detAdj(M);
  assert.strictEqual(r.det, 18n);
  // M · adj = det · I
  for (let i = 0; i < 3; i++) for (let j = 0; j < 3; j++) {
    let s = 0n;
    for (let k = 0; k < 3; k++) s += BigInt(M[i][k]) * r.adj[k][j];
    assert.strictEqual(s, i === j ? 18n : 0n);
  }
  assert.strictEqual(L.detAdj([[1, 2], [2, 4]]).det, 0n);
}

// ---- encode / decode of the arrows between two frozen vertices
for (let t = 0; t < 2000; t++) {
  const a = { uij: rnd(3), uji: rnd(3), fij: rnd(3), fji: rnd(3) };
  const [x, y] = L.encodePair(a);
  const d = L.decodePair(x, y);
  assert(d.ok);
  assert.deepStrictEqual(L.encodePair(d), [x, y]);
  assert(d.uij * d.uji === 0 && d.uij * d.fji === 0 && d.uji * d.fij === 0, 'reduced');
}

// ---- random ice quivers with frozen arrows
function randomIce(n) {
  const frozen = Array.from({ length: n }, () => Math.random() < 0.4);
  frozen[0] = false;
  const B = Array.from({ length: n }, () => new Array(n).fill(0));
  const FF = Array.from({ length: n }, () => new Array(n).fill(0));
  for (let i = 0; i < n; i++) for (let j = i + 1; j < n; j++) {
    if (Math.random() < 0.5) continue;
    if (frozen[i] && frozen[j]) {
      const a = { uij: 0, uji: 0, fij: 0, fji: 0 };
      const k = rnd(4);
      if (k === 0) a.uij = 1 + rnd(2); else if (k === 1) a.uji = 1 + rnd(2); else if (k === 2) a.fij = 1; else a.fji = 1 + rnd(2);
      [FF[i][j], FF[j][i]] = L.encodePair(a);
    } else {
      const v = rnd(5) - 2;
      B[i][j] = v; B[j][i] = -v || 0;
    }
  }
  return { B, FF, frozen };
}
let defined = 0;
for (let t = 0; t < 1500; t++) {
  const n = 2 + rnd(6);
  const q = randomIce(n);
  const E = L.eulerMatrix(q.B, q.FF, q.frozen);
  const cp = L.compatiblePair(E);
  const un = q.frozen.map((f, i) => (f ? -1 : i)).filter((i) => i >= 0);
  const v = un[rnd(un.length)];

  // Lemma 4.2: E_v B̂ E_vᵀ is the Euler matrix of the extended Fomin–Zelevinsky mutation
  const m = L.mutateIce(q.B, q.FF, q.frozen, v);
  const E2 = L.mutateEuler(E, v);
  assert.deepStrictEqual(L.eulerMatrix(m.B, m.FF, q.frozen), E2, 'Lemma 4.2');
  // the unfrozen part mutates by the usual Fomin–Zelevinsky rule
  for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) {
    if (i === j || (q.frozen[i] && q.frozen[j])) continue;
    const b = q.B;
    const want = (i === v || j === v) ? -b[i][j] : b[i][j] + Math.max(b[i][v], 0) * Math.max(b[v][j], 0) - Math.max(-b[i][v], 0) * Math.max(-b[v][j], 0);
    assert.strictEqual(m.B[i][j], want || 0, 'FZ rule');
  }
  // mutation is an involution
  const back = L.mutateIce(m.B, m.FF, q.frozen, v);
  assert.deepStrictEqual(back.B, q.B); assert.deepStrictEqual(back.FF, q.FF);
  assert.deepStrictEqual(L.mutateEuler(E2, v), E);

  if (!cp.ok) { assert.strictEqual(L.compatiblePair(E2).ok, false); continue; }
  defined++;
  // Proposition 4.1: Λ is skew-symmetric and B̃ᵀΛ = 2|det B̂| (I | 0)
  assert.deepStrictEqual(cp.Lambda, T(cp.Lambda).map((r) => r.map((x) => -x || 0)), 'skew');
  assert.strictEqual(cp.type, 2 * Math.abs(cp.det));
  assert(L.compatibilityCheck(E, cp.Lambda, q.frozen, cp.type).ok, 'Proposition 4.1');
  // Proposition 4.3: Λ of the mutated quiver is E_vᵀ Λ E_v, same determinant
  const cp2 = L.compatiblePair(E2);
  assert.strictEqual(cp2.det, cp.det);
  assert.deepStrictEqual(cp2.Lambda, L.mutateLambda(cp.Lambda, E, v), 'Proposition 4.3');
}
assert(defined > 200);

// ---- Dynkin data
{
  const counts = { A1: 1, A2: 3, A3: 6, A4: 10, A5: 15, D4: 12, D5: 20, D6: 30, E6: 36, E7: 63, E8: 120 };
  for (const [name, N] of Object.entries(counts)) {
    const d = L.dynkin(name[0], +name.slice(1));
    assert.strictEqual(d.N, N, name);
  }
  const a3 = L.dynkin('A', 3);
  assert.deepStrictEqual(L.checkWord(a3, [1, 2, 3, 2, 1, 2]).star, [0, 3, 2, 1]);
  assert.strictEqual(L.checkWord(a3, [1, 2, 1, 2]).reduced, false);
  assert.strictEqual(L.checkWord(a3, [1, 2, 3]).longest, false);
  assert.strictEqual(L.adaptedTo(a3, [1, 2, 3, 2, 1, 2]).adapted, false);
  assert.strictEqual(L.adaptedTo(a3, [3, 1, 2, 3, 1, 2]).adapted, true);
  // i* : D4 trivial, D5 swaps the two short legs, E6 the diagram automorphism
  const star = (t, n) => { const d = L.dynkin(t, n); return L.checkWord(d, L.adaptedWord(d, L.orientation(d, 'linear'))).star.slice(1); };
  assert.deepStrictEqual(star('D', 4), [1, 2, 3, 4]);
  assert.deepStrictEqual(star('D', 5), [1, 2, 3, 5, 4]);
  assert.deepStrictEqual(star('E', 6), [6, 2, 5, 4, 3, 1]);
  assert.deepStrictEqual(star('E', 7), [1, 2, 3, 4, 5, 6, 7]);
}

// ---- Example 5.6 of the paper: Δ = A3, w0 = (1,2,3,2,1,2), [a,b] = [−2,6]
{
  const q = L.kkopQuiver(L.dynkin('A', 3), [1, 2, 3, 2, 1, 2], -2, 6);
  const row = (i) => q.verts.filter((v) => v.row === i).map((v) => v.s);
  assert.deepStrictEqual(row(1), [1, 5]);
  assert.deepStrictEqual(row(2), [-2, 0, 2, 4, 6]);
  assert.deepStrictEqual(row(3), [-1, 3]);
  assert.deepStrictEqual(q.verts.filter((v) => v.frozen).map((v) => v.s), [-2, -1, 1]);
  assert.strictEqual(q.cycles.length, 6, 'six chordless cycles');
  assert.deepStrictEqual(q.arrows.filter((e) => e.frozen).map((e) => [q.verts[e.from].s, q.verts[e.to].s]), [[-2, -1], [-2, 1]]);
}

// ---- Q^[a,b](w0): frozen arrows only between frozen vertices; det B̂ = ±1 when Γ̂ is known to be proper
function randomReducedWord(d) {
  for (;;) {
    const w = [];
    while (w.length < d.N) {
      const cand = [];
      for (let i = 1; i <= d.n; i++) if (L.checkWord(d, w.concat([i])).reduced) cand.push(i);
      w.push(cand[rnd(cand.length)]);
    }
    return w;
  }
}
let knownProper = 0, conjectural = 0;
for (const [t, n] of [['A', 1], ['A', 2], ['A', 3], ['A', 4], ['A', 5], ['D', 4], ['D', 5], ['E', 6]]) {
  const d = L.dynkin(t, n);
  const words = [];
  for (const kind of ['linear', 'linear-rev', 'bipartite', 'bipartite-rev']) {
    const w = L.adaptedWord(d, L.orientation(d, kind));
    assert(w && L.checkWord(d, w).longest, 'adapted word is a reduced word of w0');
    const ad = L.adaptedTo(d, w);
    assert(ad.adapted, 'and it is adapted');
    assert.deepStrictEqual(ad.or, L.orientation(d, kind), 'to the orientation it came from');
    words.push(w);
  }
  for (let k = 0; k < (d.N > 20 ? 2 : 6); k++) words.push(randomReducedWord(d));
  for (const w of words) {
    for (let rep = 0; rep < 4; rep++) {
      const a = -rnd(d.N + 3), b = a + rnd(Math.min(2 * d.N + 2, 26));
      const q = L.kkopQuiver(d, w, a, b);
      assert(q.ok);
      assert.strictEqual(q.verts.filter((v) => v.frozen).length, Math.min(d.n, new Set(q.verts.map((v) => v.row)).size));
      q.arrows.forEach((e) => { if (e.frozen) assert(q.verts[e.from].frozen && q.verts[e.to].frozen); });
      q.arrows.forEach((e) => { if (q.verts[e.from].frozen && q.verts[e.to].frozen) assert(e.frozen, 'arrows between frozen vertices are frozen'); });
      const E = L.eulerMatrix(q.B, q.FF, q.frozen);
      const cp = L.compatiblePair(E);
      if (q.proper.known) {
        knownProper++;
        // Lemma 4.4: proper ⇒ B̂ invertible over Z
        assert(cp.ok && Math.abs(cp.det) === 1, t + n + ' [' + a + ',' + b + '] ' + w.join('') + ': det = ' + cp.det);
        assert(L.compatibilityCheck(E, cp.Lambda, q.frozen, 2).ok);
      } else {
        conjectural++;
        // Conjecture 8.1 predicts the same; record a failure loudly rather than hide it
        assert(cp.ok && Math.abs(cp.det) === 1, 'Conjecture 8.1 would fail?! ' + t + n + ' [' + a + ',' + b + '] ' + w.join(','));
      }
      if (q.adapted.adapted) {
        // KR labels: within a row, p increases by 2 and r decreases by 1 from left to right
        for (let i = 1; i <= d.n; i++) {
          const rowv = q.verts.map((v, x) => [v, q.kr[x]]).filter(([v]) => v.row === i);
          rowv.forEach(([, k], x) => {
            assert.strictEqual(k.r, rowv.length - x);
            if (x) assert.strictEqual(k.p, rowv[x - 1][1].p + 2);
            assert.strictEqual(((k.p - q.adapted.xi[i]) % 2 + 2) % 2, 0);
          });
        }
      }
    }
  }
}
assert(knownProper > 100);

// ---- Theorem D for sl2, checked against the monoidal side directly.
// For U_q'(sl2^), KR modules correspond to q-strings; d(V, W) = 0 if the strings are in general
// position and 1 otherwise, and D shifts a string by h = 2 (one step in units of q^2).
// Λ(V, W) = d(V, W) + Σ_{n ≥ 1} (−1)^{n−1} ( d(V, D^{−n} W) − d(V, D^{n} W) )     (Proposition 5.1)
{
  const general = (S, U) => {
    const [s1, e1] = S, [s2, e2] = U;
    const unionIsString = Math.max(s1, s2) <= Math.min(e1, e2) + 1;
    const nested = (s1 <= s2 && e2 <= e1) || (s2 <= s1 && e1 <= e2);
    return !unionIsString || nested;
  };
  const dinv = (S, U) => (general(S, U) ? 0 : 1);
  const shift = (S, k) => [S[0] + k, S[1] + k];
  const LambdaMonoidal = (S, U) => {
    let v = dinv(S, U);
    for (let k = 1; k <= 40; k++) v += (k % 2 ? 1 : -1) * (dinv(S, shift(U, -k)) - dinv(S, shift(U, k)));
    return v;
  };
  const d = L.dynkin('A', 1);
  for (let m = 0; m <= 7; m++) {
    const q = L.kkopQuiver(d, [1], 0, m);
    const cp = L.compatiblePair(L.eulerMatrix(q.B, q.FF, q.frozen));
    assert.strictEqual(Math.abs(cp.det), 1);
    // V_s = W_{r, q^p}: the string p/2, p/2 + 1, …, p/2 + r − 1
    const str = q.kr.map((k) => [k.p / 2, k.p / 2 + k.r - 1]);
    for (let x = 0; x <= m; x++) for (let y = 0; y <= m; y++) {
      assert.strictEqual(cp.Lambda[x][y], LambdaMonoidal(str[x], str[y]), 'sl2: Λ(V_' + x + ', V_' + y + ')');
    }
  }
}

console.log('lambda tests passed (' + knownProper + ' proper cases, ' + conjectural + ' conjectural cases, all with det = ±1)');

// ---- stages of the step-by-step display end at the mutated quiver
for (let t = 0; t < 300; t++) {
  const n = 2 + rnd(5);
  const q = randomIce(n);
  const st = L.mutationStages(q.B, q.FF, q.frozen, 0);
  const m = L.mutateIce(q.B, q.FF, q.frozen, 0);
  const a = L.arrowsOf(m.B, m.FF, q.frozen);
  assert.deepStrictEqual(st[4].A, a.U); assert.deepStrictEqual(st[4].Fz, a.Fz);
  // stage 3 minus its highlighted arrows, plus the merged frozen arrows, is the result
  for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) {
    if (i === j) continue;
    const merged = st[3].hlF[j][i];
    const cancelledPairs = Math.min(st[3].A[i][j], st[3].A[j][i]);
    assert.strictEqual(st[3].A[i][j] - st[3].hl[i][j], a.U[i][j], 'unfrozen after stage 3');
    assert.strictEqual(st[3].Fz[i][j] - st[3].hlF[i][j] + merged, a.Fz[i][j], 'frozen after stage 3');
    assert(cancelledPairs <= st[3].hl[i][j]);
  }
}
console.log('stages ok');

// ---- Lemma 5.10: for an adapted word, Q^[a,b](w0) is a piece of the Hernandez–Leclerc quiver:
// with the spectral parameters p_s used for the KR labels, s → t iff
//   (rows adjacent and p_t = p_s + 1)  or  (same row and p_t = p_s − 2).
{
  let checked = 0;
  for (const [t, n] of [['A', 2], ['A', 3], ['A', 4], ['D', 4], ['D', 5], ['E', 6]]) {
    const d = L.dynkin(t, n);
    for (const kind of ['linear', 'linear-rev', 'bipartite', 'bipartite-rev']) {
      const w = L.adaptedWord(d, L.orientation(d, kind));
      for (const [a, b] of [[-2 * d.N, 0], [-d.N - 3, 5], [1, d.N + 4], [-7, -2]]) {
        const q = L.kkopQuiver(d, w, a, b);
        const has = q.verts.map(() => q.verts.map(() => false));
        q.arrows.forEach((e) => { has[e.from][e.to] = true; });
        for (let x = 0; x < q.verts.length; x++) for (let y = 0; y < q.verts.length; y++) {
          if (x === y) continue;
          const u = q.verts[x], v = q.verts[y], pu = q.kr[x].p, pv = q.kr[y].p;
          const hl = (d.adj[u.row][v.row] && pv === pu + 1) || (u.row === v.row && pv === pu - 2);
          if (u.frozen && v.frozen) { if (hl) assert(has[x][y], 'HL arrow between frozen vertices is present'); }
          else assert.strictEqual(has[x][y], !!hl, t + n + ' ' + kind + ' [' + a + ',' + b + ']: ' + u.s + '→' + v.s);
          checked++;
        }
        // all cycles of the potential have length 3 in the adapted case (proof of Corollary 8.8)
        q.cycles.forEach((c) => assert.strictEqual(c.length, 3));
      }
    }
  }
  console.log('Hernandez–Leclerc quiver ok (' + checked + ' pairs)');
}
