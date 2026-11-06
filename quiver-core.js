/*
 * quiver-core.js — 箭图（quiver）与冰箭图（ice quiver）变异的纯数学部分。
 *
 * 箭图用斜对称整数矩阵 B 表示：B[i][j] = (i→j 的箭头数) − (j→i 的箭头数)。
 * frozen[i] 为 true 表示顶点 i 是冰冻（frozen）顶点：不能在该点变异，
 * 并且冰冻顶点之间的箭头被忽略（恒为 0）。
 *
 * 在可变顶点 k 处的变异 μ_k（Fomin–Zelevinsky）：
 *   b'_ij = −b_ij                                    若 i = k 或 j = k
 *   b'_ij = b_ij + (|b_ik|·b_kj + b_ik·|b_kj|) / 2    否则
 * 等价的组合描述：
 *   (1) 对每条路径 i → k → j，添加一条箭头 i → j；
 *   (2) 反转所有与 k 相连的箭头；
 *   (3) 删去所有 2-圈（以及冰冻顶点之间的箭头）。
 */
(function (root) {
  'use strict';

  function zeros(n) {
    const M = [];
    for (let i = 0; i < n; i++) M.push(new Array(n).fill(0));
    return M;
  }

  function clone(M) {
    return M.map(function (r) { return r.slice(); });
  }

  /** 斜对称矩阵 → 非负箭头计数矩阵 A[i][j] = i→j 的箭头数 */
  function toCounts(B) {
    return B.map(function (r) { return r.map(function (v) { return v > 0 ? v : 0; }); });
  }

  /** 矩阵变异公式 */
  function mutate(B, k, frozen) {
    frozen = frozen || [];
    if (frozen[k]) throw new Error('不能在冰冻顶点处变异');
    const n = B.length;
    const C = zeros(n);
    for (let i = 0; i < n; i++) {
      for (let j = 0; j < n; j++) {
        if (i === k || j === k) {
          C[i][j] = -B[i][j];
        } else {
          C[i][j] = B[i][j] + (Math.abs(B[i][k]) * B[k][j] + B[i][k] * Math.abs(B[k][j])) / 2;
        }
        if (frozen[i] && frozen[j]) C[i][j] = 0;
        if (C[i][j] === 0) C[i][j] = 0; // 去掉 -0
      }
    }
    return C;
  }

  /**
   * 变异的分步演示：返回若干阶段，每个阶段含
   *   A     : 非负箭头计数矩阵（允许 2-圈）
   *   hl    : 每对 (i,j) 中需要高亮的箭头数
   *   color : 高亮颜色名
   *   title / text : 说明文字
   */
  function mutationStages(B, k, frozen) {
    frozen = frozen || [];
    const n = B.length;
    const A0 = toCounts(B);

    // 阶段 0：高亮经过 k 的箭头
    const hl0 = zeros(n);
    for (let i = 0; i < n; i++) {
      hl0[i][k] = A0[i][k];
      hl0[k][i] = A0[k][i];
    }

    // 阶段 1：对每条 i→k→j 添加 i→j
    const A1 = clone(A0);
    const hl1 = zeros(n);
    let added = 0;
    for (let i = 0; i < n; i++) {
      if (i === k) continue;
      for (let j = 0; j < n; j++) {
        if (j === k || j === i) continue;
        const m = A0[i][k] * A0[k][j];
        if (m > 0) {
          A1[i][j] += m;
          hl1[i][j] = m;
          added += m;
        }
      }
    }

    // 阶段 2：反转与 k 相连的箭头
    const A2 = clone(A1);
    const hl2 = zeros(n);
    for (let j = 0; j < n; j++) {
      if (j === k) continue;
      A2[k][j] = A1[j][k];
      A2[j][k] = A1[k][j];
      hl2[k][j] = A2[k][j];
      hl2[j][k] = A2[j][k];
    }

    // 阶段 3：标出要删除的 2-圈及冰冻顶点之间的箭头
    const hl3 = zeros(n);
    let cancelled = 0;
    for (let i = 0; i < n; i++) {
      for (let j = i + 1; j < n; j++) {
        if (frozen[i] && frozen[j]) {
          hl3[i][j] = A2[i][j];
          hl3[j][i] = A2[j][i];
        } else {
          const m = Math.min(A2[i][j], A2[j][i]);
          hl3[i][j] = m;
          hl3[j][i] = m;
        }
        cancelled += hl3[i][j] + hl3[j][i];
      }
    }

    // 阶段 4：最终结果
    const A4 = toCounts(mutate(B, k, frozen));

    return [
      { A: A0, hl: hl0, color: 'blue', title: '原箭图',
        text: '在顶点 k 处变异。蓝色为与 k 相连的箭头。' },
      { A: A1, hl: hl1, color: 'green', title: '第 1 步：补全路径',
        text: added > 0
          ? '对每条路径 i → k → j，添加一条箭头 i → j（绿色，共 ' + added + ' 条）。'
          : '没有经过 k 的路径 i → k → j，这一步不添加箭头。' },
      { A: A2, hl: hl2, color: 'orange', title: '第 2 步：反转',
        text: '把所有与 k 相连的箭头反向（橙色）。' },
      { A: A2, hl: hl3, color: 'red', title: '第 3 步：删除 2-圈',
        text: cancelled > 0
          ? '成对删除方向相反的箭头（2-圈），并删除冰冻顶点之间的箭头（红色，共 ' + cancelled + ' 条）。'
          : '没有 2-圈需要删除。' },
      { A: A4, hl: zeros(n), color: 'none', title: '结果 μ_k(Q)',
        text: '变异完成。再次在 k 处变异会回到原箭图（μ_k 是对合）。' }
    ];
  }


  // ------------------------------------------------------------------ 路代数
  /*
   * 路代数 kQ（或截断商 kQ/R^L，R 为箭头生成的理想）。
   * 约定（以表示的语言）：
   *   P(i)_j 的基 = 从 i 到 j 的路      （不可分解投射模，顶为 S(i)）
   *   I(i)_j 的基 = 从 j 到 i 的路      （不可分解内射模，基座为 S(i)）
   *   S(i)   = 在 i 处为 k，其余为 0    （单模）
   * 长度为 l 的 i→j 路的条数 = (A^l)_ij，A 为箭头计数矩阵。
   * 计数用 BigInt，避免多重箭头时溢出；无穷维用 null 表示。
   */
  function matMulBig(X, Y) {
    const n = X.length;
    const Z = [];
    for (let i = 0; i < n; i++) {
      const row = new Array(n).fill(0n);
      for (let k = 0; k < n; k++) {
        const x = X[i][k];
        if (x === 0n) continue;
        for (let j = 0; j < n; j++) if (Y[k][j] !== 0n) row[j] += x * Y[k][j];
      }
      Z.push(row);
    }
    return Z;
  }

  function isZeroBig(M) {
    return M.every(function (r) { return r.every(function (x) { return x === 0n; }); });
  }

  /**
   * @param A     非负箭头计数矩阵（A[i][j] = i→j 的箭头数）
   * @param opts  { truncate: L }  L 为正整数时计算 kQ/R^L（长度 ≥ L 的路为 0）
   * @return {
   *   n, acyclic, finite, truncate,
   *   paths : n×n，paths[i][j] = i→j 的路数（BigInt；无穷为 null）
   *   powers: [A^0, A^1, ...] 非零的幂（有限情形全部；无穷情形前若干个）
   *   dim   : 代数总维数（BigInt 或 null）
   *   loewy : Loewy 长度（有限时 = 最长路长度 + 1）
   *   onCycle: 位于有向圈上的顶点
   * }
   */
  function pathAlgebra(A, opts) {
    opts = opts || {};
    const n = A.length;
    const L = opts.truncate && opts.truncate > 0 ? Math.floor(opts.truncate) : null;
    const A1 = A.map(function (r) { return r.map(function (x) { return BigInt(x); }); });
    const I = [];
    for (let i = 0; i < n; i++) {
      const r = new Array(n).fill(0n);
      r[i] = 1n;
      I.push(r);
    }

    // 可达性（长度 ≥ 1）与有向圈上的顶点
    const reach = A.map(function (r) { return r.map(function (x) { return x > 0; }); });
    for (let k = 0; k < n; k++)
      for (let i = 0; i < n; i++)
        if (reach[i][k])
          for (let j = 0; j < n; j++)
            if (reach[k][j]) reach[i][j] = true;
    const onCycle = [];
    for (let i = 0; i < n; i++) if (reach[i][i]) onCycle.push(i);
    const acyclic = onCycle.length === 0;

    // 需要的幂的个数：有限情形最多 n 个（A^n = 0），截断时 L 个
    const finite = acyclic || L != null;
    const maxPow = L != null ? (acyclic ? Math.min(L, n) : L) : (acyclic ? n : Math.max(n, 6));
    const powers = [I];
    let cur = I;
    for (let l = 1; l < maxPow; l++) {
      cur = matMulBig(cur, A1);
      if (isZeroBig(cur)) break;
      powers.push(cur);
    }

    const paths = [];
    for (let i = 0; i < n; i++) {
      const row = [];
      for (let j = 0; j < n; j++) {
        if (finite) {
          let s = 0n;
          for (let l = 0; l < powers.length; l++) s += powers[l][i][j];
          row.push(s);
        } else {
          // 无穷当且仅当存在圈上顶点 c 使 i →* c →* j
          let inf = false;
          for (const c of onCycle) {
            if ((i === c || reach[i][c]) && (c === j || reach[c][j])) { inf = true; break; }
          }
          if (inf) row.push(null);
          else {
            let s = 0n;
            for (let l = 0; l < powers.length; l++) s += powers[l][i][j];
            row.push(s);
          }
        }
      }
      paths.push(row);
    }

    let dim = 0n;
    for (let i = 0; i < n && dim !== null; i++)
      for (let j = 0; j < n; j++) {
        if (paths[i][j] === null) { dim = null; break; }
        dim += paths[i][j];
      }

    return {
      n: n,
      acyclic: acyclic,
      finite: finite,
      truncate: L,
      onCycle: onCycle,
      paths: paths,
      powers: powers,
      dim: dim,
      loewy: finite ? powers.length : null
    };
  }

  /** P(i) 的维数向量（第 i 行）*/
  function projectiveDim(pa, i) { return pa.paths[i].slice(); }
  /** I(i) 的维数向量（第 i 列）*/
  function injectiveDim(pa, i) { return pa.paths.map(function (r) { return r[i]; }); }

  /** 维数向量求和（null 表示无穷）*/
  function totalDim(v) {
    let s = 0n;
    for (const x of v) { if (x === null) return null; s += x; }
    return s;
  }

  /**
   * P(i) 的根层（radical layers）：第 l 层 rad^l P(i) / rad^{l+1} P(i) 的维数向量
   * = 从 i 出发、长度恰为 l 的路的终点统计。I(i) 的基座层类似（kind = 'I'）。
   */
  function layers(pa, i, kind) {
    return pa.powers.map(function (M) {
      return kind === 'I' ? M.map(function (r) { return r[i]; }) : M[i].slice();
    });
  }

  /** 检查矩阵是否斜对称 */
  function isSkewSymmetric(B) {
    for (let i = 0; i < B.length; i++)
      for (let j = 0; j < B.length; j++)
        if (B[i][j] !== -B[j][i]) return false;
    return true;
  }

  const api = {
    zeros: zeros,
    clone: clone,
    toCounts: toCounts,
    mutate: mutate,
    mutationStages: mutationStages,
    isSkewSymmetric: isSkewSymmetric,
    pathAlgebra: pathAlgebra,
    projectiveDim: projectiveDim,
    injectiveDim: injectiveDim,
    totalDim: totalDim,
    layers: layers
  };

  if (typeof module !== 'undefined' && module.exports) module.exports = api;
  else root.QuiverCore = api;
})(typeof window !== 'undefined' ? window : this);
