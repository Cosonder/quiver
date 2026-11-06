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

// ---- 有向圈的具体例子
{
  const c = AR.findCycle([[0, 1, 0], [0, 0, 1], [1, 0, 0]]);
  assert.strictEqual(c.length, 3);
  for (let t = 0; t < 3; t++) assert.strictEqual([[0, 1, 0], [0, 0, 1], [1, 0, 0]][c[t]][c[(t + 1) % 3]], 1, 'cycle edges');
  assert.strictEqual(AR.findCycle([[0, 1], [0, 0]]), null);
  console.log('findCycle ok');
}

// ---- 正则分支：Euclidean 型的管
{
  const cycleEdges = (m) => Array.from({ length: m }, (_, i) => [i, (i + 1) % m]);
  const cases = [];
  for (let m = 2; m <= 7; m++) cases.push({ name: 'Ã' + (m - 1), n: m, e: cycleEdges(m), ranks: null });
  for (let k = 4; k <= 8; k++) {
    // D̃_k：k+1 个顶点，两个三叉点各带两片叶子
    const e = [];
    for (let i = 0; i < k - 2; i++) e.push([i, i + 1]);
    e.push([0, k - 1], [k - 2, k]);
    // k = 4 时 0 与 2 并不相邻 —— 用星形
    const edges = k === 4 ? [[0, 1], [0, 2], [0, 3], [0, 4]] : (() => {
      const f = []; // 主干 0 - 1 - … - (k-4)，0 上挂 k-3, k-2，末端挂 k-1, k
      for (let i = 0; i < k - 4; i++) f.push([i, i + 1]);
      f.push([0, k - 3], [0, k - 2], [k - 4, k - 1], [k - 4, k]);
      return f;
    })();
    cases.push({ name: 'D̃' + k, n: k + 1, e: edges, ranks: [2, 2, k - 2].filter((r) => r > 1).sort((a, b) => a - b) });
  }
  [[[2, 2, 2], [2, 3, 3], 'Ẽ6'], [[1, 3, 3], [2, 3, 4], 'Ẽ7'], [[1, 2, 5], [2, 3, 5], 'Ẽ8']].forEach(([arms, ranks, name]) => {
    const s = star(arms); cases.push({ name, n: s.n, e: s.e, ranks });
  });
  for (const c of cases) {
    for (let rep = 0; rep < 12; rep++) {
      const perm = shuffle(c.n);
      const A = Array.from({ length: c.n }, () => new Array(c.n).fill(0));
      let cw = 0, ccw = 0;
      c.e.forEach(([a, b]) => {
        if (Math.random() < 0.5) { A[perm[a]][perm[b]] += 1; cw++; } else { A[perm[b]][perm[a]] += 1; ccw++; }
      });
      if (c.name.startsWith('Ã') && (cw === 0 || ccw === 0)) { // 有向圈，换一个定向
        const [a, b] = c.e[0];
        if (cw === 0) { A[perm[b]][perm[a]] -= 1; A[perm[a]][perm[b]] += 1; cw = 1; ccw--; }
        else { A[perm[a]][perm[b]] -= 1; A[perm[b]][perm[a]] += 1; ccw = 1; cw--; }
      }
      const res = AR.arQuiver(A, { layers: 3 });
      assert(res.ok && res.comps.length === 1 && res.comps[0].kind === 'euclidean', c.name);
      const reg = res.comps[0].regular;
      assert(reg && reg.ok, c.name + ' regular');
      const ranks = reg.tubes.map((t) => t.rank);
      const expect = c.ranks || [cw, ccw].filter((r) => r > 1).sort((a, b) => a - b);
      assert.deepStrictEqual(ranks, expect, c.name + ' tube ranks');
      assert.strictEqual(ranks.reduce((s, r) => s + r - 1, 0), c.n - 2, c.name + ' Σ(r−1) = n−2');
      // δ 在 Tits 型的根基中
      assert.strictEqual(titsBig(A, reg.delta), 0n);
      const t = AR.tubes(A, res.P, res.comps[0].verts);
      for (const tube of reg.tubes) {
        const r = tube.rank;
        for (let k = 0; k < r; k++) {
          // τ 的作用：Φ(simples[k]) = simples[k+1]
          assert.deepStrictEqual(t.phi(tube.simples[k]), tube.simples[(k + 1) % r]);
          for (let l = 1; l <= r + 1; l++) {
            const d = AR.tubeModuleDim(tube, k, l);
            assert.strictEqual(euler(A, reg.delta, d), 0, 'defect 0');
            assert.strictEqual(titsBig(A, d), l % r === 0 ? 0n : 1n, 'real / imaginary root');
          }
        }
      }
      // Φ 与编织算法一致：dim τX = Φ dim X
      res.tau.forEach(({ from, to }) => assert.deepStrictEqual(t.phi(res.nodes[from].dim), res.nodes[to].dim, 'Φ = τ'));
    }
  }
  console.log('tubes ok');
}

// ---- 导出范畴与丛范畴
{
  const keyset = (arr) => new Set(arr.map((v) => v.join(',')));
  for (const t of dynkin) {
    for (let rep = 0; rep < 8; rep++) {
      const A = fromEdges(t.n, t.e, shuffle(t.n));
      const mod = AR.arQuiver(A);
      const modSet = keyset(mod.nodes.map((x) => x.dim));
      // D^b，平移 −1..2：每个平移次数恰好是 mod kQ 的一份拷贝
      const D = AR.derivedQuiver(A, { category: 'derived', dmin: -1, dmax: 2 });
      for (let d = -1; d <= 2; d++) {
        const layer = D.nodes.filter((x) => x.deg === d);
        assert.strictEqual(layer.length, t.count, t.name + ' copy size [' + d + ']');
        assert.deepStrictEqual(keyset(layer.map((x) => x.dim)), modSet, t.name + ' copy = mod');
        layer.forEach((x) => assert.deepStrictEqual(x.cls, x.dim.map((v) => (d % 2 === 0 ? v : -v || 0))));
      }
      // τ⁻¹ I(j) = P(j)[1]
      const at = new Map(D.nodes.map((x) => [x.r + ':' + x.i, x]));
      D.nodes.filter((x) => x.deg === 0 && x.inj >= 0).forEach((x) => {
        const y = at.get((x.r + 1) + ':' + x.i);
        assert(y && y.deg === 1, 'next is shifted');
        assert.deepStrictEqual(y.dim, D.P[x.inj], t.name + ' Nakayama');
      });
      // AR 公式在 K₀ 中：<[X], y> = −<y, [τX]>
      D.tau.forEach(({ from, to }) => {
        for (let j = 0; j < t.n; j++) {
          const e = new Array(t.n).fill(0); e[j] = 1;
          assert.strictEqual(euler(A, D.nodes[from].cls, e) + euler(A, e, D.nodes[to].cls), 0, 'AR formula D^b');
        }
      });
      // 丛范畴：不可分解对象 = 正根 + n
      const C = AR.derivedQuiver(A, { category: 'cluster' });
      assert.strictEqual(C.total, t.count + t.n, t.name + ' cluster count');
      const sp = C.nodes.filter((x) => x.shiftP >= 0 && !x.ghost).map((x) => x.shiftP).sort((a, b) => a - b);
      assert.deepStrictEqual(sp, [...Array(t.n).keys()], 'each P[1] once');
      assert.deepStrictEqual(keyset(C.nodes.filter((x) => x.shiftP < 0 && !x.ghost).map((x) => x.dim)), modSet, 'cluster modules');
      // 绕回：P(j)[1] 的 τ⁻¹ 是 P(j)
      const atC = new Map(C.nodes.map((x) => [x.r + ':' + x.i, x]));
      C.nodes.filter((x) => x.shiftP >= 0).forEach((x) => {
        const g = atC.get((x.r + 1) + ':' + x.i);
        assert(g && g.ghost && g.proj === x.shiftP, 'wrap to P');
      });
    }
  }
  // 非 Dynkin：含投射模的分支 = 预内射[−1] ∪ 预投射[0]
  for (let tcase = 0; tcase < 200; tcase++) {
    const n = 2 + Math.floor(Math.random() * 5);
    const p = shuffle(n);
    const B = Array.from({ length: n }, () => new Array(n).fill(0));
    for (let i = 0; i < n; i++) for (let j = i + 1; j < n; j++) if (Math.random() < 0.5) B[p[i]][p[j]] = 1 + (Math.random() < 0.15 ? 1 : 0);
    const D = AR.derivedQuiver(B, { category: 'derived', layers: 4 });
    const C = AR.derivedQuiver(B, { category: 'cluster', layers: 4 });
    const inf = new Set(); D.comps.forEach((c) => { if (c.kind !== 'dynkin') c.verts.forEach((v) => inf.add(v)); });
    D.nodes.filter((x) => inf.has(x.i)).forEach((x) => {
      assert.strictEqual(x.deg, x.r >= 0 ? 0 : -1, 'degree');
      if (x.r === -1) assert.deepStrictEqual(x.dim, D.I[x.i], 'τP = I[−1]');
    });
    D.tau.forEach(({ from, to }) => {
      for (let j = 0; j < n; j++) {
        const e = new Array(n).fill(0); e[j] = 1;
        assert.strictEqual(euler(B, D.nodes[from].cls, e) + euler(B, e, D.nodes[to].cls), 0, 'AR formula');
      }
    });
    C.nodes.filter((x) => inf.has(x.i)).forEach((x) => {
      if (x.r === -1) assert.strictEqual(x.shiftP, x.i, 'P[1] column');
      if (x.r === -2) assert.deepStrictEqual(x.dim, C.I[x.i], 'then I');
      if (x.r >= 0) assert.deepStrictEqual(x.dim, x.cls, 'preprojective');
    });
  }
  console.log('derived / cluster ok');
}
