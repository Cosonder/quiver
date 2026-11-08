// Run: node tests/hom.test.js
const assert = require('assert');
const AR = require('../ar-core.js');

const zeros = (n) => Array.from({ length: n }, () => Array(n).fill(0));
const unit = (n, i) => Array.from({ length: n }, (_, j) => +(i === j));
const key = (v) => v.join(',');
function oriented(n, edges, bits, perm = Array.from({ length: n }, (_, i) => i)) {
  const A = zeros(n);
  edges.forEach(([u, v], i) => {
    if ((bits >> i) & 1) [u, v] = [v, u];
    A[perm[u]][perm[v]] = 1;
  });
  return A;
}

// Independent oracle: solve Y_a f_u - f_v X_a = 0 for actual arrow matrices.
// Hom is the kernel and Ext^1 the cokernel of this hereditary two-term complex.
// Test matrices are tiny and integral; pivot tolerance only handles roundoff.
function rank(matrix, columns) {
  const a = matrix.map((row) => row.slice());
  let r = 0;
  for (let c = 0; c < columns && r < a.length; c++) {
    let p = r;
    while (p < a.length && Math.abs(a[p][c]) < 1e-9) p++;
    if (p === a.length) continue;
    [a[r], a[p]] = [a[p], a[r]];
    const pivot = a[r][c];
    for (let j = c; j < columns; j++) a[r][j] /= pivot;
    for (let i = r + 1; i < a.length; i++) {
      const f = a[i][c];
      for (let j = c; j < columns; j++) a[i][j] -= f * a[r][j];
    }
    r++;
  }
  return r;
}
function linearHomExt(A, X, Y) {
  let variables = 0;
  const offset = X.dim.map((d, v) => {
    const start = variables;
    variables += d * Y.dim[v];
    return start;
  });
  const equations = [];
  for (let u = 0; u < A.length; u++) for (let v = 0; v < A.length; v++) {
    if (!A[u][v]) continue;
    assert.strictEqual(A[u][v], 1, 'oracle only used for simply-laced test quivers');
    const xa = X.maps[u + ':' + v], ya = Y.maps[u + ':' + v];
    for (let b = 0; b < Y.dim[v]; b++) for (let a = 0; a < X.dim[u]; a++) {
      const row = Array(variables).fill(0);
      for (let c = 0; c < Y.dim[u]; c++) row[offset[u] + c * X.dim[u] + a] += ya[b][c];
      for (let c = 0; c < X.dim[v]; c++) row[offset[v] + b * X.dim[v] + c] -= xa[c][a];
      equations.push(row);
    }
  }
  const r = rank(equations, variables);
  return { hom: variables - r, ext: equations.length - r };
}
function thinRepresentation(A, dim) {
  const maps = {};
  A.forEach((row, u) => row.forEach((m, v) => {
    if (m) maps[u + ':' + v] = Array.from({ length: dim[v] }, () => Array(dim[u]).fill(1));
  }));
  return { dim, maps };
}
function checkRepresentations(A, representations, context) {
  const r = AR.dynkinHomExt(A);
  assert(r.ok, context + ': ' + r.reason);
  const byDim = new Map(representations.map((x) => [key(x.dim), x]));
  assert.strictEqual(r.ar.nodes.length, representations.length, context + ' completeness');
  r.ar.nodes.forEach((x) => {
    assert(byDim.has(key(x.dim)), context + ' known representation ' + key(x.dim));
    r.ar.nodes.forEach((y) => {
      const exact = linearHomExt(A, byDim.get(key(x.dim)), byDim.get(key(y.dim)));
      const label = context + ' ' + key(x.dim) + ' → ' + key(y.dim);
      assert.strictEqual(r.hom[x.id][y.id], exact.hom, label + ' Hom');
      assert.strictEqual(r.ext[x.id][y.id], exact.ext, label + ' Ext');
    });
  });
  return r;
}

// Every orientation of A1,...,A6, including reversed vertex labels. All
// indecomposables are interval representations with identity internal maps.
for (let n = 1; n <= 6; n++) {
  const edges = Array.from({ length: n - 1 }, (_, i) => [i, i + 1]);
  for (let bits = 0; bits < 2 ** (n - 1); bits++) {
    const perm = Array.from({ length: n }, (_, i) => n - 1 - i);
    const A = oriented(n, edges, bits, perm);
    const reps = [];
    for (let lo = 0; lo < n; lo++) for (let hi = lo; hi < n; hi++) {
      const dim = Array(n).fill(0);
      for (let i = lo; i <= hi; i++) dim[perm[i]] = 1;
      reps.push(thinRepresentation(A, dim));
    }
    checkRepresentations(A, reps, 'A' + n + ' orientation ' + bits);
  }
}

// All eight D4 orientations, using explicit representations, including the
// highest-root object with a 2-dimensional central space. Distinct incoming
// image lines / outgoing kernel lines make this object indecomposable.
for (let bits = 0; bits < 8; bits++) {
  const A = oriented(4, [[0, 1], [0, 2], [0, 3]], bits);
  const reps = [];
  for (let leaves = 0; leaves < 8; leaves++) {
    reps.push(thinRepresentation(A, [1, leaves & 1, (leaves >> 1) & 1, (leaves >> 2) & 1]));
  }
  for (let i = 1; i <= 3; i++) reps.push(thinRepresentation(A, unit(4, i)));
  const highest = { dim: [2, 1, 1, 1], maps: {} };
  const vectors = [[1, 0], [0, 1], [1, 1]];
  const covectors = [[0, 1], [1, 0], [1, -1]];
  for (let i = 1; i <= 3; i++) {
    if (A[i][0]) highest.maps[i + ':0'] = vectors[i - 1].map((x) => [x]);
    else highest.maps['0:' + i] = [covectors[i - 1]];
  }
  reps.push(highest);
  checkRepresentations(A, reps, 'D4 orientation ' + bits);
}

function euler(A, x, y) {
  let value = 0;
  for (let i = 0; i < A.length; i++) {
    value += x[i] * y[i];
    for (let j = 0; j < A.length; j++) value -= A[i][j] * x[i] * y[j];
  }
  return value;
}
function checkInvariants(A, context) {
  const r = AR.dynkinHomExt(A);
  assert(r.ok, context + ': ' + r.reason);
  const nodes = r.ar.nodes;
  const find = (dim) => nodes.find((x) => key(x.dim) === key(dim)).id;
  const position = new Map(r.order.map((id, i) => [id, i]));
  assert.strictEqual(position.size, nodes.length, context + ' topological order completeness');
  for (const edge of r.ar.edges) assert(position.get(edge.from) < position.get(edge.to), context + ' topological edge');
  for (const x of nodes) for (const y of nodes) {
    const h = r.hom[x.id][y.id], e = r.ext[x.id][y.id];
    assert(Number.isSafeInteger(h) && h >= 0, context + ' Hom nonnegative integer');
    assert(Number.isSafeInteger(e) && e >= 0, context + ' Ext nonnegative integer');
    assert.strictEqual(r.euler[x.id][y.id], euler(A, x.dim, y.dim), context + ' Euler');
    assert.strictEqual(h - e, r.euler[x.id][y.id], context + ' Euler identity');
    assert.strictEqual(r.compatible[x.id][y.id], e === 0 && r.ext[y.id][x.id] === 0, context + ' two-sided compatibility');
    if (x.comp !== y.comp) {
      assert.strictEqual(h, 0, context + ' cross-component Hom');
      assert.strictEqual(e, 0, context + ' cross-component Ext');
    }
  }
  for (const x of nodes) {
    assert.strictEqual(r.hom[x.id][x.id], 1, context + ' exceptional endomorphisms');
    assert.strictEqual(r.ext[x.id][x.id], 0, context + ' rigid');
    for (let i = 0; i < A.length; i++) {
      const p = find(r.ar.P[i]), inj = find(r.ar.I[i]);
      assert.strictEqual(r.hom[p][x.id], x.dim[i], context + ' Hom(P_i,X)');
      assert.strictEqual(r.hom[x.id][inj], x.dim[i], context + ' Hom(X,I_i)');
      assert.strictEqual(r.ext[p][x.id], 0, context + ' projective Ext');
      assert.strictEqual(r.ext[x.id][inj], 0, context + ' injective Ext');
    }
  }
  for (const { from: x, to: tx } of r.ar.tau) {
    for (const y of nodes) assert.strictEqual(r.ext[x][y.id], r.hom[y.id][tx], context + ' hereditary AR duality');
  }
  for (let i = 0; i < A.length; i++) for (let j = 0; j < A.length; j++) {
    const si = find(unit(A.length, i)), sj = find(unit(A.length, j));
    assert.strictEqual(r.hom[si][sj], +(i === j), context + ' simple Hom');
    assert.strictEqual(r.ext[si][sj], A[i][j], context + ' simple Ext arrow convention');
  }
}
function star(arms) {
  const edges = [];
  let n = 1;
  arms.forEach((length) => {
    let previous = 0;
    for (let i = 0; i < length; i++) { edges.push([previous, n]); previous = n++; }
  });
  return { n, edges };
}
for (const arms of [[1, 1, 1], [1, 1, 3], [1, 1, 5], [1, 2, 2], [1, 2, 3], [1, 2, 4]]) {
  const { n, edges } = star(arms);
  for (const bits of [0, 0x55, 0xaa, 0xff]) {
    const perm = Array.from({ length: n }, (_, i) => (i + 2) % n);
    checkInvariants(oriented(n, edges, bits, perm), 'D/E ' + arms + ' orientation ' + bits);
  }
}
checkInvariants([[0]], 'A1');
checkInvariants(oriented(6, [[0, 1], [2, 3], [3, 4]], 2), 'A2 ⊔ A3 ⊔ A1');

// A concrete D4 pair detects implementations which reduce all Hom values to
// Boolean reachability, and checks the asymmetric argument convention.
{
  const A = oriented(4, [[0, 1], [0, 2], [0, 3]], 0);
  const r = AR.dynkinHomExt(A);
  const m = r.ar.nodes.find((x) => key(x.dim) === '2,1,1,1').id;
  const s = r.ar.nodes.find((x) => key(x.dim) === '1,0,0,0').id;
  assert.strictEqual(r.hom[m][s], 2);
  assert.strictEqual(r.ext[m][s], 0);
  assert.strictEqual(r.hom[s][m], 0);
  assert.strictEqual(r.ext[s][m], 1);
}

// Unsupported algebras must fail explicitly rather than return a partial table.
for (const A of [[], [[0, 2], [0, 0]], [[0, 3], [0, 0]], [[0, 1], [1, 0]], [[1]], [[0, 1, 1], [0, 0, 1], [0, 0, 0]]]) {
  const r = AR.dynkinHomExt(A);
  assert.strictEqual(r.ok, false, 'unsupported ' + JSON.stringify(A));
  assert(r.reason, 'unsupported input has a reason');
  assert(!r.hom && !r.ext, 'no misleading partial tables');
}
for (const A of [null, {}, [0], [[0, 1]], [[0, -1], [0, 0]], [[0, 0.5], [0, 0]], [[0, Infinity], [0, 0]], [[0, NaN], [0, 0]]]) {
  const r = AR.dynkinHomExt(A);
  assert.strictEqual(r.ok, false, 'invalid input');
  assert(r.reason, 'invalid input has a reason');
}
{
  const A = oriented(32, Array.from({ length: 31 }, (_, i) => [i, i + 1]), 0);
  const before = JSON.stringify(A);
  const r = AR.dynkinHomExt(A);
  assert.strictEqual(r.ok, false);
  assert.strictEqual(r.reason, 'too-large', '528 objects exceed the documented 512-object cap');
  assert(!r.hom && !r.ext, 'size limit returns no incomplete results');
  assert.strictEqual(JSON.stringify(A), before, 'input is not mutated');
}
assert.strictEqual(AR.dynkinHomExt([[0, 2, 0], [0, 0, 0], [0, 0, 0]]).ok, false,
  'a Dynkin component does not make a mixed affine/Dynkin quiver supported');

console.log('all Dynkin Hom/Ext tests passed (independent A/D4 representations and A/D/E invariants)');
