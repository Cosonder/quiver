// 运行：node tests/core.test.js
const assert = require('assert');
const Q = require('../quiver-core.js');

function eq(a, b, msg) { assert.deepStrictEqual(a, b, msg); }

// A3 线性 1→2→3，在 2 处变异得到三角循环
let B = [[0, 1, 0], [-1, 0, 1], [0, -1, 0]];
eq(Q.mutate(B, 1), [[0, -1, 1], [1, 0, -1], [-1, 1, 0]], 'A3 mutate at 2');

// 对合性 + 分步演示终态与公式一致（随机测试，含冰冻顶点）
function rnd(n, frozen) {
  const M = Q.zeros(n);
  for (let i = 0; i < n; i++) for (let j = i + 1; j < n; j++) {
    if (frozen[i] && frozen[j]) continue;
    const v = Math.floor(Math.random() * 5) - 2;
    M[i][j] = v; M[j][i] = -v || 0;
  }
  return M;
}
for (let t = 0; t < 2000; t++) {
  const n = 2 + Math.floor(Math.random() * 6);
  const frozen = Array.from({ length: n }, () => Math.random() < 0.3);
  frozen[0] = false;
  const M = rnd(n, frozen);
  const k = 0;
  const M1 = Q.mutate(M, k, frozen);
  assert(Q.isSkewSymmetric(M1), 'skew');
  eq(Q.mutate(M1, k, frozen), M, 'involution');
  const st = Q.mutationStages(M, k, frozen);
  const A3 = st[3].A.map((r, i) => r.map((v, j) => v - st[3].hl[i][j]));
  eq(A3, Q.toCounts(M1), 'stages agree');
  eq(st[4].A, Q.toCounts(M1), 'final stage');
}

// Markov 箭图在任意点变异保持不变（同构，此处矩阵取负号后等价）
const markov = [[0, 2, -2], [-2, 0, 2], [2, -2, 0]];
eq(Q.mutate(markov, 0), [[0, -2, 2], [2, 0, -2], [-2, 2, 0]], 'markov');

assert.throws(() => Q.mutate(B, 1, [false, true, false]));

// ---- 路代数 ----
const cnt = (B) => Q.toCounts(B);
// A3 线性 1→2→3：dim kQ = 6；P(1)=(1,1,1)，P(3)=(0,0,1)，I(1)=(1,0,0)，I(3)=(1,1,1)
let pa = Q.pathAlgebra(cnt([[0, 1, 0], [-1, 0, 1], [0, -1, 0]]));
assert(pa.acyclic && pa.dim === 6n);
eq(Q.projectiveDim(pa, 0), [1n, 1n, 1n]);
eq(Q.projectiveDim(pa, 2), [0n, 0n, 1n]);
eq(Q.injectiveDim(pa, 0), [1n, 0n, 0n]);
eq(Q.injectiveDim(pa, 2), [1n, 1n, 1n]);
eq(pa.loewy, 3);
eq(Q.layers(pa, 0, 'P'), [[1n, 0n, 0n], [0n, 1n, 0n], [0n, 0n, 1n]]);
// Kronecker：dim = 4；P(1) = (1,2)
pa = Q.pathAlgebra(cnt([[0, 2], [-2, 0]]));
eq(pa.dim, 4n); eq(Q.projectiveDim(pa, 0), [1n, 2n]);
// 多重箭头的路计数：1 ⇉ 2 ⇉ 3（各 2 条）→ 1→3 有 4 条路
pa = Q.pathAlgebra(cnt([[0, 2, 0], [-2, 0, 2], [0, -2, 0]]));
eq(Q.projectiveDim(pa, 0), [1n, 2n, 4n]); eq(pa.dim, 1n + 2n + 4n + 1n + 2n + 1n);
// 三角循环：无穷维；截断 R^2=0 时 dim = 3 + 3 = 6；R^3=0 时 dim = 9
const cyc = [[0, 1, -1], [-1, 0, 1], [1, -1, 0]];
pa = Q.pathAlgebra(cnt(cyc));
assert(!pa.acyclic && pa.dim === null && pa.paths[0][1] === null);
eq(Q.pathAlgebra(cnt(cyc), { truncate: 2 }).dim, 6n);
eq(Q.pathAlgebra(cnt(cyc), { truncate: 3 }).dim, 9n);
// 部分无穷：1 → (2⇄ 圈不可能，用 2→3→4→2) ，5 孤立
const M5 = Q.zeros(5);
[[0, 1], [1, 2], [2, 3], [3, 1]].forEach(([a, b]) => { M5[a][b] = 1; M5[b][a] = -1; });
pa = Q.pathAlgebra(cnt(M5));
assert(pa.paths[0][1] === null && pa.paths[1][0] === 0n && pa.paths[4][4] === 1n && pa.paths[0][0] === 1n);
// 随机无圈箭图：Σ dim P(i) = Σ dim I(i) = dim kQ，且与暴力枚举路一致
for (let t = 0; t < 300; t++) {
  const n = 1 + Math.floor(Math.random() * 6);
  const A = Q.zeros(n);
  for (let i = 0; i < n; i++) for (let j = i + 1; j < n; j++) if (Math.random() < 0.5) A[i][j] = Math.floor(Math.random() * 3);
  const r = Q.pathAlgebra(A);
  const brute = (i) => { let s = 1n; for (let j = 0; j < n; j++) if (A[i][j]) s += BigInt(A[i][j]) * brute(j); return s; };
  let sp = 0n, si = 0n;
  for (let i = 0; i < n; i++) {
    assert.strictEqual(Q.totalDim(Q.projectiveDim(r, i)), brute(i));
    sp += Q.totalDim(Q.projectiveDim(r, i)); si += Q.totalDim(Q.injectiveDim(r, i));
  }
  assert(sp === r.dim && si === r.dim);
}
console.log('all tests passed');
