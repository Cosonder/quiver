// 运行：node tests/ar.test.js
const assert = require('assert');
const AR = require('../ar-core.js');

// Euler 形式 <x,y> = Σ x_i y_i − Σ_{i→j} x_i y_j；遗传代数上 <dim X, dim Y> = dim Hom − dim Ext¹
function euler(A, x, y) {
  let s = 0;
  for (let i = 0; i < x.length; i++) { s += x[i] * y[i]; for (let j = 0; j < x.length; j++) s -= A[i][j] * x[i] * y[j]; }
  return s;
}
function titsBig(A, x) {
  let s = 0n;
  for (let i = 0; i < x.length; i++) { s += BigInt(x[i]) ** 2n; for (let j = 0; j < x.length; j++) s -= BigInt(A[i][j]) * BigInt(x[i]) * BigInt(x[j]); }
  return s;
}
function fromEdges(n, edges, perm) {
  const A = Array.from({ length: n }, () => new Array(n).fill(0));
  edges.forEach(([a, b, m]) => {
    let [u, v] = Math.random() < 0.5 ? [a, b] : [b, a];
    if (perm) { u = perm[u]; v = perm[v]; }
    A[u][v] += m || 1;
  });
  return A;
}
const shuffle = (n) => { const p = [...Array(n).keys()]; for (let i = n - 1; i > 0; i--) { const j = Math.floor(Math.random() * (i + 1)); [p[i], p[j]] = [p[j], p[i]]; } return p; };
const path = (n) => Array.from({ length: n - 1 }, (_, i) => [i, i + 1]);
const star = (arms) => { // 中心 0，三条臂
  const e = []; let next = 1;
  arms.forEach((len) => { let prev = 0; for (let t = 0; t < len; t++) { e.push([prev, next]); prev = next++; } });
  return { n: next, e };
};

function checkAR(A, res) {
  assert(res.ok);
  const n = A.length;
  const byId = res.nodes;
  // 每个模的维数向量非负非零，且是实根 q = 1
  byId.forEach((nd) => {
    assert(nd.dim.every((x) => x >= 0) && nd.dim.some((x) => x > 0), 'positive');
    assert.strictEqual(titsBig(A, nd.dim), 1n, 'real root ' + nd.dim);
  });
  // <dim P(i), y> = y_i，<y, dim I(i)> = y_i
  for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) {
    const e = new Array(n).fill(0); e[j] = 1;
    assert.strictEqual(euler(A, res.P[i], e), i === j ? 1 : 0, 'proj');
    assert.strictEqual(euler(A, e, res.I[i]), i === j ? 1 : 0, 'inj');
  }
  // AR 公式：<x, y> = −<y, τx>，对所有 y
  res.tau.forEach(({ from, to }) => {
    const x = byId[from].dim, tx = byId[to].dim;
    for (let j = 0; j < n; j++) {
      const e = new Array(n).fill(0); e[j] = 1;
      assert.strictEqual(euler(A, x, e) + euler(A, e, tx), 0, 'AR formula');
    }
  });
  // 网格关系：对每个有 τ 的 X，dim X + dim τX = Σ (τX 的直接后继)
  res.tau.forEach(({ from, to }) => {
    const sum = new Array(n).fill(0);
    res.edges.filter((e) => e.from === to).forEach((e) => byId[e.to].dim.forEach((x, t) => { sum[t] += e.mult * x; }));
    assert.deepStrictEqual(sum, byId[from].dim.map((x, t) => x + byId[to].dim[t]), 'mesh');
  });
}

// ---- Dynkin：不可分解模个数 = 正根个数，且维数向量两两不同
const dynkin = [];
for (let n = 1; n <= 8; n++) dynkin.push({ name: 'A' + n, n, e: path(n), count: n * (n + 1) / 2 });
for (let n = 4; n <= 8; n++) { const s = star([1, 1, n - 3]); dynkin.push({ name: 'D' + n, n: s.n, e: s.e, count: n * (n - 1) }); }
[[[1, 2, 2], 36, 'E6'], [[1, 2, 3], 63, 'E7'], [[1, 2, 4], 120, 'E8']].forEach(([arms, count, name]) => { const s = star(arms); dynkin.push({ name, n: s.n, e: s.e, count }); });
for (const t of dynkin) {
  for (let rep = 0; rep < 15; rep++) {
    const A = fromEdges(t.n, t.e, shuffle(t.n));
    const res = AR.arQuiver(A);
    assert(res.finite, t.name);
    assert.strictEqual(res.comps[0].count, t.count, t.name + ' classify count');
    assert.strictEqual(res.total, t.count, t.name + ' knitting count');
    assert.strictEqual(new Set(res.nodes.map((x) => x.dim.join(','))).size, t.count, t.name + ' distinct');
    assert(res.nodes.every((x) => x.kind === 'P'));
    // 每个内射模恰好出现一次
    for (let i = 0; i < t.n; i++) assert(res.nodes.some((x) => x.dim.join() === res.I[i].join()), 'injective appears');
    checkAR(A, res);
  }
}

// ---- 分类
const cls = (n, e) => AR.classify(fromEdges(n, e), [...Array(n).keys()]).name;
assert.strictEqual(cls(2, [[0, 1, 2]]), 'Ã₁');
assert.strictEqual(cls(2, [[0, 1, 3]]), 'wild');
assert.strictEqual(cls(4, [[0, 1], [1, 2], [2, 3], [3, 0]]), 'Ã₃');
assert.strictEqual(cls(5, [[0, 1], [0, 2], [0, 3], [0, 4]]), 'D̃₄');
assert.strictEqual(cls(6, [[0, 1], [0, 2], [0, 3], [3, 4], [3, 5]]), 'D̃₅');
assert.strictEqual(cls(star([2, 2, 2]).n, star([2, 2, 2]).e), 'Ẽ₆');
assert.strictEqual(cls(star([1, 3, 3]).n, star([1, 3, 3]).e), 'Ẽ₇');
assert.strictEqual(cls(star([1, 2, 5]).n, star([1, 2, 5]).e), 'Ẽ₈');
assert.strictEqual(cls(star([2, 2, 3]).n, star([2, 2, 3]).e), 'wild');
assert.strictEqual(cls(3, [[0, 1, 2], [1, 2]]), 'wild');

// ---- Kronecker 1 ⇉ 2：预投射分支 (0,1), (1,2), (2,3), (3,4) …
let A = [[0, 2], [0, 0]];
let res = AR.arQuiver(A, { layers: 4 });
assert(!res.finite && res.total === null);
const prepDims = res.nodes.filter((x) => x.kind === 'P').map((x) => x.dim.join(','));
assert.deepStrictEqual(prepDims, ['1,2', '0,1', '3,4', '2,3', '5,6', '4,5', '7,8', '6,7']);
const injDims = res.nodes.filter((x) => x.kind === 'I').map((x) => x.dim.join(','));
assert.deepStrictEqual(injDims.slice(0, 2), ['1,0', '2,1']);
checkAR(A, res);

// ---- 随机 Euclidean / wild / 不连通的无圈箭图：AR 公式与网格关系
for (let t = 0; t < 300; t++) {
  const n = 2 + Math.floor(Math.random() * 6);
  const p = shuffle(n);
  const B = Array.from({ length: n }, () => new Array(n).fill(0));
  for (let i = 0; i < n; i++) for (let j = i + 1; j < n; j++) if (Math.random() < 0.4) B[p[i]][p[j]] = 1 + (Math.random() < 0.15 ? 1 : 0);
  res = AR.arQuiver(B, { layers: 5 });
  checkAR(B, res);
}

// ---- 有向圈：拒绝
assert.strictEqual(AR.arQuiver([[0, 1], [1, 0]]).reason, 'cyclic');
console.log('all AR tests passed');
