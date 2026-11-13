/*
 * lambda-core.js — the constructions of
 *
 *   R. Canesin, P. Cao, G. Janssens,
 *   "Additive categorification of the monoidal Λ-invariant", arXiv:2605.03925v2.
 *
 * Everything here is combinatorial and exact (BigInt where needed).
 *
 * (§4.1) An ice quiver (Q, F) may have arrows between frozen vertices, and each such
 * arrow is either frozen or unfrozen. Its Euler matrix B̂ is
 *     b̂_ii = 0 (i unfrozen), 1 (i frozen),
 *     b̂_ij = #{unfrozen arrows i→j} − #{all arrows j→i}      (i ≠ j).
 * If det B̂ ≠ 0, then  Λ = |det B̂| · (B̂^{-T} − B̂^{-1})  is a skew-symmetric integer
 * matrix and (B̃, Λ) is a compatible pair of type 2|det B̂|·I, where B̃ consists of the
 * unfrozen columns of B̂ (Proposition 4.1). Mutation at an unfrozen vertex v is
 *     μ_v(B̂) = E_v B̂ E_vᵀ,   μ_v(Λ) = E_vᵀ Λ E_v              (Lemma 4.2, Prop. 4.3).
 *
 * (§5.3) For a simply-laced Dynkin diagram Δ, a reduced word w₀ of the longest element
 * and an interval [a, b], the ice quiver Q^[a,b](w₀) with its frozen subquiver and
 * potential (the initial seed of Kashiwara–Kim–Oh–Park).
 *
 * In this file a quiver is stored as
 *     B  : skew-symmetric matrix, entries between two frozen vertices are 0,
 *     FF : matrix that is 0 except between two distinct frozen vertices, where it holds
 *          the Euler-matrix entry b̂_ij.
 * For reduced ice quivers (no unfrozen 2-cycles, no half-frozen 2-cycles) the pair of
 * entries (b̂_ij, b̂_ji) determines the arrows between i and j, see decodePair.
 */
(function (root) {
  'use strict';

  // ------------------------------------------------------------------ exact linear algebra
  const absBig = (x) => (x < 0n ? -x : x);
  function gcdBig(a, b) { a = absBig(a); b = absBig(b); while (b) { const t = a % b; a = b; b = t; } return a; }
  function frac(n, d) {
    if (d < 0n) { n = -n; d = -d; }
    const g = gcdBig(n, d) || 1n;
    return [n / g, d / g];
  }
  const fmul = (x, y) => frac(x[0] * y[0], x[1] * y[1]);
  const fsub = (x, y) => frac(x[0] * y[1] - y[0] * x[1], x[1] * y[1]);
  const fdiv = (x, y) => frac(x[0] * y[1], x[1] * y[0]);

  /**
   * Determinant and adjugate of an integer matrix, exactly.
   * @return { det: BigInt, adj: BigInt[][] | null }  with adj = det · M^{-1} (null if det = 0)
   */
  function detAdj(M) {
    const n = M.length;
    if (!n) return { det: 1n, adj: [] };
    const A = M.map((r, i) => r.map((x) => [BigInt(x), 1n]).concat(r.map((_, j) => [i === j ? 1n : 0n, 1n])));
    let det = [1n, 1n];
    for (let c = 0; c < n; c++) {
      let p = -1;
      for (let r = c; r < n; r++) if (A[r][c][0] !== 0n) { p = r; break; }
      if (p < 0) return { det: 0n, adj: null };
      if (p !== c) { const t = A[p]; A[p] = A[c]; A[c] = t; det = [-det[0], det[1]]; }
      const pv = A[c][c];
      det = fmul(det, pv);
      for (let j = 0; j < 2 * n; j++) A[c][j] = fdiv(A[c][j], pv);
      for (let r = 0; r < n; r++) {
        if (r === c || A[r][c][0] === 0n) continue;
        const f = A[r][c];
        for (let j = 0; j < 2 * n; j++) if (A[c][j][0] !== 0n) A[r][j] = fsub(A[r][j], fmul(f, A[c][j]));
      }
    }
    const d = det[0]; // det is an integer
    const adj = [];
    for (let i = 0; i < n; i++) {
      const row = [];
      for (let j = 0; j < n; j++) {
        const x = A[i][n + j];
        row.push(d * x[0] / x[1]);
      }
      adj.push(row);
    }
    return { det: d, adj: adj };
  }

  const zeros = (n, m) => Array.from({ length: n }, () => new Array(m == null ? n : m).fill(0));
  const transpose = (M) => (M.length ? M[0].map((_, j) => M.map((r) => r[j])) : []);
  function matMul(X, Y) {
    const n = X.length, m = Y.length ? Y[0].length : 0, k = Y.length;
    const Z = zeros(n, m);
    for (let i = 0; i < n; i++) for (let t = 0; t < k; t++) {
      const x = X[i][t];
      if (x) for (let j = 0; j < m; j++) Z[i][j] += x * Y[t][j];
    }
    return Z;
  }
  const toNum = (x) => {
    const v = Number(x);
    if (!Number.isSafeInteger(v)) throw new Error('integer overflow');
    return v;
  };

  // ------------------------------------------------------------------ §4.1 Euler matrix and Λ
  /** Arrows between two frozen vertices i, j from the Euler entries x = b̂_ij, y = b̂_ji. */
  function decodePair(x, y) {
    const out = { uij: 0, uji: 0, fij: 0, fji: 0, ok: x + y <= 0 };
    if (x > 0) { out.uij = x; out.fij = 0 - (x + y); }
    else if (y > 0) { out.uji = y; out.fji = 0 - (x + y); }
    else { out.fji = 0 - x; out.fij = 0 - y; }
    return out;
  }
  /** Inverse of decodePair (also performs the reductions of the extended FZ mutation). */
  function encodePair(a) {
    return [a.uij - a.uji - a.fji, a.uji - a.uij - a.fij];
  }

  function eulerMatrix(B, FF, frozen) {
    const n = B.length;
    const E = zeros(n);
    for (let i = 0; i < n; i++) {
      for (let j = 0; j < n; j++) {
        if (i === j) E[i][j] = frozen[i] ? 1 : 0;
        else if (frozen[i] && frozen[j]) E[i][j] = FF ? FF[i][j] : 0;
        else E[i][j] = B[i][j];
      }
    }
    return E;
  }

  /** Split an Euler matrix back into (B, FF). */
  function splitEuler(E, frozen) {
    const n = E.length;
    const B = zeros(n), FF = zeros(n);
    for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) {
      if (i === j) continue;
      if (frozen[i] && frozen[j]) FF[i][j] = E[i][j];
      else B[i][j] = E[i][j];
    }
    return { B: B, FF: FF };
  }

  /**
   * The compatible pair of an ice quiver.
   * @return { ok, det (Number), Lambda (Number[][]), type (Number) } or { ok: false, det: 0 }
   */
  function compatiblePair(E) {
    const n = E.length;
    const r = detAdj(E);
    if (r.det === 0n) return { ok: false, det: 0 };
    const sgn = r.det < 0n ? -1n : 1n;
    const L = zeros(n);
    for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) L[i][j] = toNum(sgn * (r.adj[j][i] - r.adj[i][j]));
    const det = toNum(r.det);
    return { ok: true, det: det, Lambda: L, type: 2 * Math.abs(det) };
  }

  /** Bᵀ̃ Λ for the unfrozen columns of E; compatible iff it equals (type·I | 0). */
  function compatibilityCheck(E, L, frozen, type) {
    const n = E.length;
    const un = [];
    for (let i = 0; i < n; i++) if (!frozen[i]) un.push(i);
    const P = un.map((v) => {
      const row = new Array(n).fill(0);
      for (let k = 0; k < n; k++) if (E[k][v]) for (let j = 0; j < n; j++) row[j] += E[k][v] * L[k][j];
      return row;
    });
    const ok = P.every((row, a) => row.every((x, j) => x === (j === un[a] ? type : 0)));
    return { ok: ok, product: P, unfrozen: un };
  }

  /** The matrix E_v of §4.1 (it is E_- of Berenstein–Zelevinsky). */
  function Ev(E, v) {
    const n = E.length;
    const M = zeros(n);
    for (let i = 0; i < n; i++) M[i][i] = 1;
    for (let i = 0; i < n; i++) if (i !== v) M[i][v] = Math.max(E[i][v], 0);
    M[v][v] = -1;
    return M;
  }
  function mutateEuler(E, v) {
    const M = Ev(E, v);
    return matMul(matMul(M, E), transpose(M)).map((r) => r.map((x) => x || 0));
  }
  function mutateLambda(L, E, v) {
    const M = Ev(E, v);
    return matMul(matMul(transpose(M), L), M).map((r) => r.map((x) => x || 0));
  }

  /** Arrow counts of (B, FF): U[i][j] unfrozen arrows i→j, Fz[i][j] frozen arrows i→j. */
  function arrowsOf(B, FF, frozen) {
    const n = B.length;
    const U = zeros(n), Fz = zeros(n);
    for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) {
      if (i === j) continue;
      if (frozen[i] && frozen[j]) {
        if (i < j && FF) {
          const d = decodePair(FF[i][j], FF[j][i]);
          U[i][j] = d.uij; U[j][i] = d.uji; Fz[i][j] = d.fij; Fz[j][i] = d.fji;
        }
      } else if (B[i][j] > 0) U[i][j] = B[i][j];
    }
    return { U: U, Fz: Fz };
  }

  /**
   * The mutation of an ice quiver in stages, for the step-by-step display.
   * Each stage: { A (unfrozen arrow counts), Fz (frozen arrow counts), hl, hlF (how many of
   * them to highlight), color, title, text }.
   */
  function mutationStages(B, FF, frozen, v) {
    const n = B.length;
    const cp = (M) => M.map((r) => r.slice());
    const a0 = arrowsOf(B, FF, frozen);
    const U0 = a0.U, Fz = a0.Fz;
    const hl0 = zeros(n);
    for (let i = 0; i < n; i++) { hl0[i][v] = U0[i][v]; hl0[v][i] = U0[v][i]; }
    const U1 = cp(U0), hl1 = zeros(n);
    let added = 0;
    for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) {
      if (i === v || j === v || i === j) continue;
      const m = U0[i][v] * U0[v][j];
      if (m) { U1[i][j] += m; hl1[i][j] = m; added += m; }
    }
    const U2 = cp(U1), hl2 = zeros(n);
    for (let j = 0; j < n; j++) {
      if (j === v) continue;
      U2[v][j] = U1[j][v]; U2[j][v] = U1[v][j];
      hl2[v][j] = U2[v][j]; hl2[j][v] = U2[j][v];
    }
    const hl3 = zeros(n), hlF3 = zeros(n);
    let cancelled = 0, merged = 0;
    for (let i = 0; i < n; i++) for (let j = i + 1; j < n; j++) {
      const m = Math.min(U2[i][j], U2[j][i]);
      hl3[i][j] = hl3[j][i] = m;
      cancelled += m;
      const m1 = Math.min(U2[i][j] - m, Fz[j][i]);
      hl3[i][j] += m1; hlF3[j][i] += m1;
      const m2 = Math.min(U2[j][i] - m, Fz[i][j]);
      hl3[j][i] += m2; hlF3[i][j] += m2;
      merged += m1 + m2;
    }
    const mu = mutateIce(B, FF, frozen, v);
    const a4 = arrowsOf(mu.B, mu.FF, frozen);
    const zf = zeros(n);
    return [
      { A: U0, Fz: Fz, hl: hl0, hlF: zf, color: 'blue', title: 'Original quiver',
        text: 'Mutating at vertex k. Arrows incident to k are shown in blue.' },
      { A: U1, Fz: Fz, hl: hl1, hlF: zf, color: 'green', title: 'Step 1: compose paths',
        text: added ? 'For each path i → k → j, add an unfrozen arrow i → j (green, ' + added + ' in total), also between two frozen vertices.'
          : 'There is no path i → k → j through k, so no arrows are added.' },
      { A: U2, Fz: Fz, hl: hl2, hlF: zf, color: 'orange', title: 'Step 2: reverse',
        text: 'Reverse all arrows incident to k (orange).' },
      { A: U2, Fz: Fz, hl: hl3, hlF: hlF3, color: 'red', title: 'Step 3: remove 2-cycles',
        text: (cancelled ? 'Remove ' + cancelled + ' 2-cycle(s) of unfrozen arrows (red). ' : 'There are no 2-cycles of unfrozen arrows. ') +
          (merged ? 'Each 2-cycle made of an unfrozen and a frozen arrow (' + merged + ') is replaced by one frozen arrow in the direction of the unfrozen one.' : '') },
      { A: a4.U, Fz: a4.Fz, hl: zeros(n), hlF: zf, color: 'none', title: 'Result μ_k(Q)',
        text: 'Mutation complete. Mutating at k again returns the original quiver (μ_k is an involution).' }
    ];
  }

  /**
   * Extended Fomin–Zelevinsky mutation (Remark 3.2) on (B, FF), done on arrows —
   * independently of the formula E_v B̂ E_vᵀ, which the tests compare it with.
   */
  function mutateIce(B, FF, frozen, v) {
    const n = B.length;
    if (frozen[v]) throw new Error('cannot mutate at a frozen vertex');
    // arrows as counts: U[i][j] unfrozen, Fz[i][j] frozen
    const U = zeros(n), Fz = zeros(n);
    for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) {
      if (i === j) continue;
      if (frozen[i] && frozen[j]) {
        if (i < j) {
          const d = decodePair(FF[i][j], FF[j][i]);
          U[i][j] = d.uij; U[j][i] = d.uji; Fz[i][j] = d.fij; Fz[j][i] = d.fji;
        }
      } else if (B[i][j] > 0) U[i][j] = B[i][j];
    }
    // (1) compose
    const add = zeros(n);
    for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) {
      if (i === v || j === v || i === j) continue;
      add[i][j] = U[i][v] * U[v][j];
    }
    for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) U[i][j] += add[i][j];
    // (2) reverse
    for (let j = 0; j < n; j++) {
      if (j === v) continue;
      const t = U[v][j]; U[v][j] = U[j][v]; U[j][v] = t;
    }
    // (3) unfrozen 2-cycles, (4) half-frozen 2-cycles
    for (let i = 0; i < n; i++) for (let j = i + 1; j < n; j++) {
      let m = Math.min(U[i][j], U[j][i]);
      U[i][j] -= m; U[j][i] -= m;
      m = Math.min(U[i][j], Fz[j][i]);
      U[i][j] -= m; Fz[j][i] -= m; Fz[i][j] += m;
      m = Math.min(U[j][i], Fz[i][j]);
      U[j][i] -= m; Fz[i][j] -= m; Fz[j][i] += m;
    }
    const B2 = zeros(n), FF2 = zeros(n);
    for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) {
      if (i === j) continue;
      if (frozen[i] && frozen[j]) FF2[i][j] = U[i][j] - U[j][i] - Fz[j][i];
      else B2[i][j] = U[i][j] - U[j][i];
    }
    return { B: B2, FF: FF2 };
  }

  // ------------------------------------------------------------------ Dynkin diagrams and Weyl groups
  /** Simply-laced Dynkin diagram. Vertices 1..n; Bourbaki labels for E. */
  function dynkin(type, n) {
    type = String(type).toUpperCase();
    n = Math.floor(n);
    const edges = [];
    if (type === 'A') {
      if (!(n >= 1 && n <= 8)) return null;
      for (let i = 1; i < n; i++) edges.push([i, i + 1]);
    } else if (type === 'D') {
      if (!(n >= 4 && n <= 8)) return null;
      for (let i = 1; i < n - 1; i++) edges.push([i, i + 1]);
      edges.push([n - 2, n]);
    } else if (type === 'E') {
      if (!(n >= 6 && n <= 8)) return null;
      edges.push([1, 3], [2, 4], [3, 4]);
      for (let i = 4; i < n; i++) edges.push([i, i + 1]);
    } else return null;
    const adj = zeros(n + 1);
    edges.forEach(([i, j]) => { adj[i][j] = adj[j][i] = 1; });
    const d = { type: type, n: n, edges: edges, adj: adj, name: type + n };
    // positive roots (coordinates in simple roots, index 0..n-1)
    const key = (v) => v.join(',');
    const seen = new Map();
    const queue = [];
    for (let i = 1; i <= n; i++) {
      const v = new Array(n).fill(0); v[i - 1] = 1;
      seen.set(key(v), v); queue.push(v);
    }
    while (queue.length) {
      const b = queue.shift();
      for (let i = 1; i <= n; i++) {
        const c = reflect(d, i, b);
        if (c.every((x) => x >= 0) && !seen.has(key(c))) { seen.set(key(c), c); queue.push(c); }
      }
    }
    d.N = seen.size;                                  // ℓ(w₀) = number of positive roots
    d.h = 2 * d.N / n;                                // Coxeter number
    return d;
  }

  /** s_i(β) = β − (β, α_i) α_i */
  function reflect(d, i, beta) {
    let pairing = 2 * beta[i - 1];
    for (let j = 1; j <= d.n; j++) if (d.adj[i][j]) pairing -= beta[j - 1];
    const out = beta.slice();
    out[i - 1] -= pairing;
    return out;
  }
  /** (s_{i_1} ⋯ s_{i_k})(β) */
  function applyWord(d, word, beta) {
    let b = beta;
    for (let k = word.length - 1; k >= 0; k--) b = reflect(d, word[k], b);
    return b;
  }
  const simpleRoot = (d, i) => { const v = new Array(d.n).fill(0); v[i - 1] = 1; return v; };

  /**
   * Check a word in the simple reflections.
   * @return { valid, reduced, longest, star, roots, error }
   *   roots[k] = s_{i_1}⋯s_{i_{k-1}}(α_{i_k});  star[i] = i* with w₀(α_i) = −α_{i*}
   */
  function checkWord(d, word) {
    const out = { valid: true, reduced: true, longest: false, star: null, roots: [], error: null };
    if (!word.every((i) => Number.isInteger(i) && i >= 1 && i <= d.n)) {
      return Object.assign(out, { valid: false, reduced: false, error: 'letters must be vertices 1, …, ' + d.n });
    }
    for (let k = 0; k < word.length; k++) {
      const b = applyWord(d, word.slice(0, k), simpleRoot(d, word[k]));
      out.roots.push(b);
      if (!b.every((x) => x >= 0)) {
        out.reduced = false;
        out.error = 'not reduced: the prefix of length ' + (k + 1) + ' is not reduced';
        return out;
      }
    }
    out.longest = word.length === d.N;
    if (!out.longest) {
      out.error = 'reduced, but of length ' + word.length + ' instead of ℓ(w₀) = ' + d.N;
      return out;
    }
    out.star = [0];
    for (let i = 1; i <= d.n; i++) {
      const b = applyWord(d, word, simpleRoot(d, i));
      out.star.push(b.findIndex((x) => x === -1) + 1);
    }
    return out;
  }

  /** Orientation as a matrix: or[i][j] = 1 if i → j. */
  function orientation(d, kind) {
    const or = zeros(d.n + 1);
    // 2-colouring of the tree
    const col = new Array(d.n + 1).fill(-1);
    col[1] = 0;
    const st = [1];
    while (st.length) {
      const u = st.pop();
      for (let v = 1; v <= d.n; v++) if (d.adj[u][v] && col[v] < 0) { col[v] = 1 - col[u]; st.push(v); }
    }
    d.edges.forEach(([i, j]) => {
      let fwd;
      if (kind === 'linear') fwd = true;
      else if (kind === 'linear-rev') fwd = false;
      else if (kind === 'bipartite') fwd = col[i] === 0;
      else fwd = col[i] !== 0;          // 'bipartite-rev'
      if (fwd) or[i][j] = 1; else or[j][i] = 1;
    });
    return or;
  }
  const isSource = (d, or, i) => { for (let j = 1; j <= d.n; j++) if (or[j][i]) return false; return true; };
  function reflectOrientation(d, or, i) {
    for (let j = 1; j <= d.n; j++) if (or[i][j]) { or[i][j] = 0; or[j][i] = 1; }
  }

  /** A reduced word of w₀ that is a source sequence for the orientation (greedy, smallest source first). */
  function adaptedWord(d, or0) {
    const or = or0.map((r) => r.slice());
    const word = [];
    while (word.length < d.N) {
      let found = 0;
      for (let i = 1; i <= d.n && !found; i++) {
        if (!isSource(d, or, i)) continue;
        if (applyWord(d, word, simpleRoot(d, i)).every((x) => x >= 0)) found = i;
      }
      if (!found) return null;
      word.push(found);
      reflectOrientation(d, or, found);
    }
    return word;
  }

  /**
   * Is the word a source sequence for some orientation of Δ? The orientation is forced:
   * on each edge, the endpoint that occurs first must be the source.
   * @return { adapted, or, xi }   xi = height function with Q_ξ = or, normalised to min ξ = 0
   */
  function adaptedTo(d, word) {
    const first = new Array(d.n + 1).fill(Infinity);
    word.forEach((i, k) => { if (first[i] === Infinity) first[i] = k; });
    const or0 = zeros(d.n + 1);
    for (const [i, j] of d.edges) {
      if (first[i] === Infinity && first[j] === Infinity) return { adapted: false };
      if (first[i] < first[j]) or0[i][j] = 1; else or0[j][i] = 1;
    }
    const or = or0.map((r) => r.slice());
    for (const i of word) {
      if (!isSource(d, or, i)) return { adapted: false };
      reflectOrientation(d, or, i);
    }
    // height function: ξ_j = ξ_i + 1 for i → j
    const xi = new Array(d.n + 1).fill(null);
    xi[1] = 0;
    const st = [1];
    while (st.length) {
      const u = st.pop();
      for (let v = 1; v <= d.n; v++) {
        if (xi[v] !== null) continue;
        if (or0[u][v]) { xi[v] = xi[u] + 1; st.push(v); }
        else if (or0[v][u]) { xi[v] = xi[u] - 1; st.push(v); }
      }
    }
    const min = Math.min.apply(null, xi.slice(1));
    for (let i = 1; i <= d.n; i++) xi[i] -= min;
    return { adapted: true, or: or0, xi: xi };
  }

  /** Does the Weyl group element given by a reduced word have a reduced word adapted to some orientation? */
  function elementIsAdapted(d, word) {
    const n = d.n;
    const idm = () => { const M = zeros(n); for (let i = 0; i < n; i++) M[i][i] = 1; return M; };
    const S = (i) => { const M = zeros(n); for (let j = 1; j <= n; j++) { const c = reflect(d, i, simpleRoot(d, j)); for (let r = 0; r < n; r++) M[r][j - 1] = c[r]; } return M; };
    // M0 = w^{-1} = s_{i_k} ⋯ s_{i_1}
    let M0 = idm();
    for (const i of word) M0 = matMul(S(i), M0);
    const E = d.edges.length;
    for (let mask = 0; mask < (1 << E); mask++) {
      const or = zeros(n + 1);
      d.edges.forEach(([i, j], e) => { if (mask >> e & 1) or[i][j] = 1; else or[j][i] = 1; });
      let M = M0;
      let len = word.length;
      let stuck = false;
      while (len > 0 && !stuck) {
        let found = 0;
        for (let i = 1; i <= n && !found; i++) {
          if (!isSource(d, or, i)) continue;
          let neg = true;                       // w^{-1}(α_i) < 0  ⇔  i is a left descent of w
          for (let r = 0; r < n; r++) if (M[r][i - 1] > 0) neg = false;
          if (neg) found = i;
        }
        if (!found) { stuck = true; break; }
        M = matMul(M, S(found));
        reflectOrientation(d, or, found);
        len--;
      }
      if (!stuck) return true;
    }
    return false;
  }

  // ------------------------------------------------------------------ §5.3 the ice quiver Q^[a,b](w₀)
  /**
   * @param d     Dynkin diagram
   * @param word  reduced word (i_1, …, i_N) of w₀
   * @param a, b  integers, a ≤ b
   * @return {
   *   ok, error, d, word, star, a, b,
   *   verts  : [{ s, row, frozen, prev, next }]            (s = a, …, b)
   *   arrows : [{ from, to, frozen, rule }]                (indices into verts; rule 1, 2 or 3)
   *   cycles : the terms of the potential W^[a,b](w₀), each a list of vertex indices
   *   B, FF, frozen : the quiver in the format described at the top of this file
   *   adapted: { adapted, xi, … }, kr: [{ i, r, p }] (only if adapted)
   *   proper : { known, by }                                Theorem C / Proposition 8.19
   * }
   */
  function kkopQuiver(d, word, a, b) {
    const chk = checkWord(d, word);
    if (!chk.longest) return { ok: false, error: chk.error || 'not a reduced word of w₀' };
    if (!(Number.isInteger(a) && Number.isInteger(b) && a <= b)) return { ok: false, error: 'need integers a ≤ b' };
    const N = d.N, star = chk.star;
    const mod = (x, m) => ((x % m) + m) % m;
    const letter = (s) => {
      const k = Math.floor((s - 1) / N);
      const i = word[mod(s - 1, N)];
      return mod(k, 2) ? star[i] : i;
    };
    const prev = (s) => { for (let t = s - 1; t >= s - 2 * N; t--) if (letter(t) === letter(s)) return t; return -Infinity; };
    const next = (s) => { for (let t = s + 1; t <= s + 2 * N; t++) if (letter(t) === letter(s)) return t; return Infinity; };
    const verts = [];
    for (let s = a; s <= b; s++) verts.push({ s: s, row: letter(s), prev: prev(s), next: next(s), frozen: prev(s) < a });
    const at = (s) => s - a;
    const arrows = [];
    for (let x = 0; x < verts.length; x++) {
      const u = verts[x];
      if (u.prev >= a) arrows.push({ from: x, to: at(u.prev), frozen: false, rule: 1 });
      for (let y = x + 1; y < verts.length; y++) {
        const w = verts[y];
        if (!d.adj[u.row][w.row]) continue;
        const r3 = u.prev < a && w.prev < a;
        const r2 = u.prev < w.prev && w.prev < u.s;
        if (r3) arrows.push({ from: x, to: y, frozen: true, rule: 3 });
        else if (r2) arrows.push({ from: x, to: y, frozen: false, rule: 2 });
      }
    }
    const n = verts.length;
    const frozen = verts.map((v) => v.frozen);
    const B = zeros(n), FF = zeros(n);
    const has = zeros(n);
    arrows.forEach((e) => {
      has[e.from][e.to] = 1;
      if (e.frozen) FF[e.to][e.from] -= 1;            // a frozen arrow i→j gives b̂_ji = −1
      else { B[e.from][e.to] += 1; B[e.to][e.from] -= 1; }
    });
    // potential: for each arrow s → t with s < t and t unfrozen, the cycle s → t → t⁻ → ⋯ → t_l → s
    const cycles = [];
    arrows.forEach((e) => {
      if (e.rule === 1 || verts[e.to].frozen) return;
      const cyc = [e.from, e.to];
      let t = e.to;
      let closed = false;
      while (!closed && verts[t].prev >= a) {
        t = at(verts[t].prev);
        cyc.push(t);
        if (has[t][e.from]) closed = true;
      }
      if (closed) cycles.push(cyc);
    });

    const ad = adaptedTo(d, word);
    let kr = null;
    if (ad.adapted) {
      // spectral parameters: p_s = ξ_i + 2·#{1 ≤ t < s, i_t = i}  (s ≥ 1),  ξ_i − 2·#{s ≤ t ≤ 0, i_t = i}  (s ≤ 0)
      kr = verts.map((v) => {
        let p = ad.xi[v.row];
        if (v.s >= 1) { for (let t = 1; t < v.s; t++) if (letter(t) === v.row) p += 2; }
        else { for (let t = v.s; t <= 0; t++) if (letter(t) === v.row) p -= 2; }
        let r = 0;
        for (let t = v.s; t <= b; t++) if (letter(t) === v.row) r++;
        return { i: v.row, r: r, p: p };
      });
    }

    // properness of the relative Ginzburg algebra
    let proper = { known: false, by: null };
    if (ad.adapted) proper = { known: true, by: 'adapted' };
    else if ((b - a + 1) % N === 0) proper = { known: true, by: 'length' };
    else {
      const len = mod(b - a + 1, N);
      const res = [];
      for (let s = b - len + 1; s <= b; s++) res.push(letter(s));
      if (elementIsAdapted(d, res)) proper = { known: true, by: 'residue' };
    }

    return {
      ok: true, d: d, word: word, star: star, a: a, b: b,
      verts: verts, arrows: arrows, cycles: cycles, B: B, FF: FF, frozen: frozen,
      adapted: ad, kr: kr, proper: proper
    };
  }

  const api = {
    detAdj: detAdj,
    decodePair: decodePair,
    encodePair: encodePair,
    eulerMatrix: eulerMatrix,
    splitEuler: splitEuler,
    compatiblePair: compatiblePair,
    compatibilityCheck: compatibilityCheck,
    Ev: Ev,
    mutateEuler: mutateEuler,
    mutateLambda: mutateLambda,
    mutateIce: mutateIce,
    arrowsOf: arrowsOf,
    mutationStages: mutationStages,
    dynkin: dynkin,
    checkWord: checkWord,
    orientation: orientation,
    adaptedWord: adaptedWord,
    adaptedTo: adaptedTo,
    elementIsAdapted: elementIsAdapted,
    kkopQuiver: kkopQuiver
  };
  if (typeof module !== 'undefined' && module.exports) module.exports = api;
  else root.LambdaCore = api;
})(typeof window !== 'undefined' ? window : this);
