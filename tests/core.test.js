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
console.log('all tests passed');
