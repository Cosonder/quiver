/*
 * ar-core.js — 无圈箭图 Q 的路代数 kQ（遗传代数）的 Auslander–Reiten 箭图。
 *
 * 约定与 quiver-core.js 相同（表示的语言）：
 *   P(i)_j 的基 = 从 i 到 j 的路，I(i)_j 的基 = 从 j 到 i 的路。
 *   rad P(i) = ⊕_{i→j} P(j)，所以对每个箭头 i→j 有不可约映射 P(j) → P(i)；
 *   I(i)/soc = ⊕_{k→i} I(k)，所以对每个箭头 k→i 有不可约映射 I(i) → I(k)。
 *
 * 用“编织”（knitting）算法计算：在 AR 序列 0 → X → E → τ⁻¹X → 0 中
 *   dim τ⁻¹X = dim E − dim X，
 * 预投射分支中 τ^{-r}P(i) 的直接后继为
 *   τ^{-r}P(k)（对每个箭头 k→i）以及 τ^{-(r+1)}P(j)（对每个箭头 i→j），
 * 只计入已经存在的模；τ^{-r}P(i) 为内射模时轨道终止。
 * 预内射分支对偶地从 I(i) 出发计算。
 *
 * Gabriel 定理：连通 Q 为有限表示型当且仅当其底图为 Dynkin 图 A/D/E，
 * 此时预投射分支就是整个 AR 箭图，不可分解模与正根一一对应。
 * Euclidean 与 wild 型时 AR 箭图无穷：这里只给出预投射、预内射分支的前若干层，
 * 规则分支（regular components）不画出。
 */
(function (root) {
  'use strict';

  const SUB = '₀₁₂₃₄₅₆₇₈₉';
  const sub = (n) => String(n).split('').map((d) => SUB[+d]).join('');

  /** 底图的连通分支（每个分支内按下标排序）*/
  function components(A) {
    const n = A.length;
    const seen = new Array(n).fill(false);
    const comps = [];
    for (let s = 0; s < n; s++) {
      if (seen[s]) continue;
      const comp = [];
      const stack = [s];
      seen[s] = true;
      while (stack.length) {
        const u = stack.pop();
        comp.push(u);
        for (let v = 0; v < n; v++) {
          if (!seen[v] && (A[u][v] > 0 || A[v][u] > 0)) {
            seen[v] = true;
            stack.push(v);
          }
        }
      }
      comps.push(comp.sort((a, b) => a - b));
    }
    return comps;
  }

  /** 拓扑序（源点在前）；有有向圈时返回 null */
  function topoOrder(A) {
    const n = A.length;
    const indeg = new Array(n).fill(0);
    for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) if (A[i][j] > 0) indeg[j]++;
    const queue = [];
    for (let i = 0; i < n; i++) if (indeg[i] === 0) queue.push(i);
    const order = [];
    while (queue.length) {
      const u = queue.shift();
      order.push(u);
      for (let v = 0; v < n; v++) {
        if (A[u][v] > 0 && --indeg[v] === 0) queue.push(v);
      }
    }
    return order.length === n ? order : null;
  }

  /** 找出一个有向圈，返回顶点序列 [v0, v1, …, vk]（vk → v0），无圈时返回 null */
  function findCycle(A) {
    const n = A.length;
    const color = new Array(n).fill(0); // 0 未访问，1 在栈中，2 已完成
    const stack = [];
    let found = null;
    const dfs = (u) => {
      color[u] = 1;
      stack.push(u);
      for (let v = 0; v < n && !found; v++) {
        if (!(A[u][v] > 0)) continue;
        if (color[v] === 1) found = stack.slice(stack.indexOf(v));
        else if (color[v] === 0) dfs(v);
      }
      stack.pop();
      color[u] = 2;
    };
    for (let s = 0; s < n && !found; s++) if (color[s] === 0) dfs(s);
    return found;
  }

  /**
   * 连通分支的底图分类。
   * 返回 { name, kind: 'dynkin' | 'euclidean' | 'wild', count }，
   * count 为 Dynkin 型时不可分解模（正根）的个数。
   */
  function classify(A, comp) {
    const n = comp.length;
    const wild = { name: 'wild', kind: 'wild', count: null };
    if (n === 1) return { name: 'A' + sub(1), kind: 'dynkin', count: 1 };
    const deg = new Map(comp.map((v) => [v, 0]));
    const nbrs = new Map(comp.map((v) => [v, []]));
    let edges = 0, maxMult = 0;
    for (let a = 0; a < n; a++) {
      for (let b = a + 1; b < n; b++) {
        const u = comp[a], v = comp[b];
        const m = A[u][v] + A[v][u];
        if (m > 0) {
          edges++;
          maxMult = Math.max(maxMult, m);
          deg.set(u, deg.get(u) + 1);
          deg.set(v, deg.get(v) + 1);
          nbrs.get(u).push(v);
          nbrs.get(v).push(u);
        }
      }
    }
    if (maxMult >= 3) return wild;
    if (maxMult === 2) return n === 2 ? { name: 'Ã' + sub(1), kind: 'euclidean', count: null } : wild;
    if (edges >= n) {
      const isCycle = edges === n && comp.every((v) => deg.get(v) === 2);
      return isCycle ? { name: 'Ã' + sub(n - 1), kind: 'euclidean', count: null } : wild;
    }
    // 树
    const degs = comp.map((v) => deg.get(v));
    const maxDeg = Math.max.apply(null, degs);
    const branch = comp.filter((v) => deg.get(v) >= 3);
    if (maxDeg <= 2) return { name: 'A' + sub(n), kind: 'dynkin', count: n * (n + 1) / 2 };
    if (maxDeg === 4) return n === 5 ? { name: 'D̃' + sub(4), kind: 'euclidean', count: null } : wild;
    if (maxDeg > 4 || branch.length > 2) return wild;
    const isLeaf = (v) => deg.get(v) === 1;
    if (branch.length === 2) {
      const ok = branch.every((b) => nbrs.get(b).filter(isLeaf).length >= 2);
      return ok ? { name: 'D̃' + sub(n - 1), kind: 'euclidean', count: null } : wild;
    }
    // 恰有一个三叉点：计算三条臂的长度
    const c = branch[0];
    const arms = nbrs.get(c).map((start) => {
      let prev = c, cur = start, len = 1;
      while (deg.get(cur) === 2) {
        const next = nbrs.get(cur).find((w) => w !== prev);
        prev = cur;
        cur = next;
        len++;
      }
      return len;
    }).sort((a, b) => a - b);
    const [p, q, r] = arms;
    if (p === 1 && q === 1) return { name: 'D' + sub(n), kind: 'dynkin', count: n * (n - 1) };
    const key = p + ',' + q + ',' + r;
    const table = {
      '1,2,2': { name: 'E' + sub(6), kind: 'dynkin', count: 36 },
      '1,2,3': { name: 'E' + sub(7), kind: 'dynkin', count: 63 },
      '1,2,4': { name: 'E' + sub(8), kind: 'dynkin', count: 120 },
      '2,2,2': { name: 'Ẽ' + sub(6), kind: 'euclidean', count: null },
      '1,3,3': { name: 'Ẽ' + sub(7), kind: 'euclidean', count: null },
      '1,2,5': { name: 'Ẽ' + sub(8), kind: 'euclidean', count: null }
    };
    return table[key] || wild;
  }

  /** Tits 二次型 q(x) = Σ x_i² − Σ_{箭头 i→j} x_i x_j */
  function titsForm(A, x) {
    let s = 0;
    for (let i = 0; i < x.length; i++) {
      s += x[i] * x[i];
      for (let j = 0; j < x.length; j++) s -= A[i][j] * x[i] * x[j];
    }
    return s;
  }

  /** 布局用的“高度” c：尽量使每个箭头 i→j 满足 c(i) − c(j) = 1 */
  function heights(A, comp) {
    const c = new Map();
    const start = comp[0];
    c.set(start, 0);
    const queue = [start];
    let ok = true;
    while (queue.length) {
      const u = queue.shift();
      for (const v of comp) {
        if (A[u][v] > 0 || A[v][u] > 0) {
          const want = A[u][v] > 0 ? c.get(u) - 1 : c.get(u) + 1;
          if (!c.has(v)) {
            c.set(v, want);
            queue.push(v);
          } else if (c.get(v) !== want || (A[u][v] > 0 && A[v][u] > 0)) {
            ok = false;
          }
        }
      }
    }
    let T = 2;
    if (!ok) {
      // 退而求其次：c(i) = 从 i 出发的最长路长度
      const memo = new Map();
      const longest = (i) => {
        if (memo.has(i)) return memo.get(i);
        let best = 0;
        for (const j of comp) if (A[i][j] > 0) best = Math.max(best, 1 + longest(j));
        memo.set(i, best);
        return best;
      };
      comp.forEach((i) => c.set(i, longest(i)));
      let maxDiff = 1;
      for (const i of comp) for (const j of comp) if (A[i][j] > 0) maxDiff = Math.max(maxDiff, c.get(i) - c.get(j));
      T = maxDiff + 1;
    }
    const min = Math.min.apply(null, comp.map((v) => c.get(v)));
    comp.forEach((v) => c.set(v, c.get(v) - min));
    return { c: c, T: T };
  }

  /** 分支内顶点的行顺序：从度数最小的顶点开始做深度优先遍历 */
  function rowOrder(A, comp) {
    const adj = (u) => comp.filter((v) => v !== u && (A[u][v] > 0 || A[v][u] > 0));
    const degree = (u) => adj(u).length;
    const start = comp.slice().sort((a, b) => degree(a) - degree(b) || a - b)[0];
    const seen = new Set();
    const order = [];
    const visit = (u) => {
      seen.add(u);
      order.push(u);
      // 先走较长的分支，使主干上的顶点相邻
      const next = adj(u).filter((v) => !seen.has(v));
      const size = (v) => {
        const s = new Set([u]);
        const st = [v];
        let cnt = 0;
        while (st.length) {
          const w = st.pop();
          if (s.has(w) || seen.has(w)) continue;
          s.add(w);
          cnt++;
          adj(w).forEach((x) => st.push(x));
        }
        return cnt;
      };
      next.sort((a, b) => size(b) - size(a) || a - b).forEach((v) => { if (!seen.has(v)) visit(v); });
    };
    visit(start);
    return order;
  }

  /**
   * 计算 AR 箭图。
   * @param A    非负箭头计数矩阵（必须无有向圈）
   * @param opts { layers }：无限表示型分支中预投射 / 预内射分支各画多少层（τ 轨道长度）
   * @return {
   *   ok, reason,
   *   finite, total, layers,
   *   P, I       : 不可分解投射 / 内射模的维数向量
   *   comps      : [{ verts, name, kind, count, rowStart, rows, gapX }]
   *   nodes      : [{ id, kind: 'P'|'I', r, i, dim, proj, inj, simple, comp, x, row }]
   *                kind 'P' 表示 τ^{-r}P(i)，kind 'I' 表示 τ^{r}I(i)；proj/inj 为同构的 P(j)/I(j) 的 j（否则 −1）
   *   edges      : [{ from, to, mult }] 不可约映射
   *   tau        : [{ from, to }]       AR 平移：from = X，to = τX
   * }
   */
  function arQuiver(A, opts) {
    opts = opts || {};
    const n = A.length;
    const R = Math.max(1, Math.min(Math.floor(opts.layers || 4), 40));
    if (!n) return { ok: false, reason: 'empty' };
    const order = topoOrder(A);
    if (!order) return { ok: false, reason: 'cyclic', cycle: findCycle(A) };
    const sinkFirst = order.slice().reverse();
    const unit = (i) => { const v = new Array(n).fill(0); v[i] = 1; return v; };

    const P = new Array(n), I = new Array(n);
    sinkFirst.forEach((i) => {
      const v = unit(i);
      for (let j = 0; j < n; j++) if (A[i][j] > 0) P[j].forEach((x, t) => { v[t] += A[i][j] * x; });
      P[i] = v;
    });
    order.forEach((i) => {
      const v = unit(i);
      for (let k = 0; k < n; k++) if (A[k][i] > 0) I[k].forEach((x, t) => { v[t] += A[k][i] * x; });
      I[i] = v;
    });

    const comps = components(A).map((verts) => Object.assign({ verts: verts }, classify(A, verts)));
    const compOf = new Array(n);
    comps.forEach((c, ci) => c.verts.forEach((v) => { compOf[v] = ci; }));
    const finite = comps.every((c) => c.kind === 'dynkin');
    const key = (v) => v.join(',');
    const projIdx = new Map(P.map((v, j) => [key(v), j]));
    const injIdx = new Map(I.map((v, j) => [key(v), j]));
    const isUnit = (v) => v.filter((x) => x !== 0).length === 1 && v.reduce((a, b) => a + b, 0) === 1;
    const limit = (i) => (comps[compOf[i]].kind === 'dynkin' ? Infinity : R);

    const nodes = [], edges = [], tau = [];
    const at = new Map(); // 'P:r:i' / 'I:r:i' → node id
    const addNode = (kind, r, i, dim) => {
      const k = key(dim);
      const node = {
        id: nodes.length, kind: kind, r: r, i: i, dim: dim,
        proj: projIdx.has(k) ? projIdx.get(k) : -1,
        inj: injIdx.has(k) ? injIdx.get(k) : -1,
        simple: isUnit(dim),
        comp: compOf[i]
      };
      nodes.push(node);
      at.set(kind + ':' + r + ':' + i, node.id);
      return node;
    };
    const addVec = (v, w, m) => { for (let t = 0; t < n; t++) v[t] += m * w[t]; };

    // ---- 预投射分支
    const prep = [P.map((v) => v.slice())];
    for (let r = 0; r < 1000; r++) {
      const cur = prep[r];
      const next = new Array(n).fill(null);
      let any = false;
      for (const i of sinkFirst) {
        const x = cur[i];
        if (!x || injIdx.has(key(x)) || r + 1 >= limit(i)) continue;
        const v = x.map((t) => -t);
        for (let k = 0; k < n; k++) if (A[k][i] > 0 && cur[k]) addVec(v, cur[k], A[k][i]);
        for (let j = 0; j < n; j++) if (A[i][j] > 0 && next[j]) addVec(v, next[j], A[i][j]);
        if (v.some((t) => t < 0) || v.every((t) => t === 0)) continue; // 不应发生
        next[i] = v;
        any = true;
      }
      if (!any) break;
      prep.push(next);
    }
    prep.forEach((layer, r) => layer.forEach((v, i) => { if (v) addNode('P', r, i, v); }));
    prep.forEach((layer, r) => {
      for (let i = 0; i < n; i++) {
        for (let j = 0; j < n; j++) {
          const m = A[i][j];
          if (!m) continue;
          const a = at.get('P:' + r + ':' + j), b = at.get('P:' + r + ':' + i), c = at.get('P:' + (r + 1) + ':' + j);
          if (a != null && b != null) edges.push({ from: a, to: b, mult: m });  // τ^{-r}P(j) → τ^{-r}P(i)
          if (b != null && c != null) edges.push({ from: b, to: c, mult: m });  // τ^{-r}P(i) → τ^{-(r+1)}P(j)
        }
        const x = at.get('P:' + r + ':' + i), y = at.get('P:' + (r + 1) + ':' + i);
        if (x != null && y != null) tau.push({ from: y, to: x });
      }
    });

    // ---- 预内射分支（只对无限表示型的分支）
    const infVerts = new Set();
    comps.forEach((c) => { if (c.kind !== 'dynkin') c.verts.forEach((v) => infVerts.add(v)); });
    if (infVerts.size) {
      const inj = [I.map((v, i) => (infVerts.has(i) ? v.slice() : null))];
      for (let r = 0; r + 1 < R; r++) {
        const cur = inj[r];
        const next = new Array(n).fill(null);
        let any = false;
        for (const i of order) {
          const x = cur[i];
          if (!x || projIdx.has(key(x))) continue;
          const v = x.map((t) => -t);
          for (let j = 0; j < n; j++) if (A[i][j] > 0 && cur[j]) addVec(v, cur[j], A[i][j]);
          for (let k = 0; k < n; k++) if (A[k][i] > 0 && next[k]) addVec(v, next[k], A[k][i]);
          if (v.some((t) => t < 0) || v.every((t) => t === 0)) continue;
          next[i] = v;
          any = true;
        }
        if (!any) break;
        inj.push(next);
      }
      inj.forEach((layer, r) => layer.forEach((v, i) => { if (v) addNode('I', r, i, v); }));
      inj.forEach((layer, r) => {
        for (let i = 0; i < n; i++) {
          for (let k = 0; k < n; k++) {
            const m = A[k][i];
            if (!m) continue;
            const a = at.get('I:' + r + ':' + i), b = at.get('I:' + r + ':' + k), c = at.get('I:' + (r + 1) + ':' + k);
            if (a != null && b != null) edges.push({ from: a, to: b, mult: m });  // τ^r I(i) → τ^r I(k)
            if (c != null && a != null) edges.push({ from: c, to: a, mult: m });  // τ^{r+1} I(k) → τ^r I(i)
          }
          const x = at.get('I:' + r + ':' + i), y = at.get('I:' + (r + 1) + ':' + i);
          if (x != null && y != null) tau.push({ from: x, to: y });
        }
      });
    }

    // ---- 布局：x 为水平坐标（单位：半个网格），row 为行号
    let rowStart = 0;
    comps.forEach((comp, ci) => {
      const h = heights(A, comp.verts);
      const rows = rowOrder(A, comp.verts);
      const rowOf = new Map(rows.map((v, t) => [v, rowStart + t]));
      const mine = nodes.filter((nd) => nd.comp === ci);
      let prepMax = -Infinity;
      mine.forEach((nd) => {
        nd.row = rowOf.get(nd.i);
        if (nd.kind === 'P') {
          nd.x = nd.r * h.T + h.c.get(nd.i);
          prepMax = Math.max(prepMax, nd.x);
        }
      });
      const injNodes = mine.filter((nd) => nd.kind === 'I');
      comp.gapX = null;
      if (injNodes.length) {
        const raw = (nd) => -nd.r * h.T + h.c.get(nd.i);
        const minRaw = Math.min.apply(null, injNodes.map(raw));
        const base = prepMax + 3 * h.T - minRaw;
        injNodes.forEach((nd) => { nd.x = base + raw(nd); });
        comp.gapX = (prepMax + base + minRaw) / 2;
      }
      comp.rowStart = rowStart;
      comp.rows = rows.length;
      rowStart += rows.length + 1;
    });

    if (opts.tubes !== false) {
      comps.forEach((c) => {
        if (c.kind !== 'euclidean') return;
        const t = tubes(A, P, c.verts);
        c.regular = t.ok
          ? { ok: true, delta: t.delta, tubes: t.tubes }
          : { ok: false, reason: t.reason, delta: t.delta || null };
      });
    }

    const total = finite ? nodes.length : null;
    return {
      ok: true, finite: finite, total: total, layers: R,
      P: P, I: I, comps: comps, nodes: nodes, edges: edges, tau: tau
    };
  }


  // ------------------------------------------------------------------ 正则分支（管）
  /*
   * Euclidean（tame）型连通箭图的正则分支是 ℙ¹ 参数族的管（tube）：
   * 除至多三个例外管外都是 rank 1 的齐次管。
   *   δ          : 零根（Tits 型的根基中的最小正向量）
   *   亏量 ∂(x)  : ⟨δ, x⟩，正则模的亏量为 0
   *   Φ          : Coxeter 变换，非投射不可分解模 X 满足 dim τX = Φ·dim X，
   *                Φ = −C·Eᵀ，其中 E = I − A（Euler 形式的矩阵），C = E⁻¹（路数矩阵）
   * 例外管中拟长度 < rank 的模的维数向量恰为满足 0 < x < δ、q(x) = 1、∂(x) = 0 的实根；
   * 它们在 Φ 下的轨道中，和为 δ 的轨道就是一个管的正则单模（轨道长度 = 管的 rank）。
   */
  function fr(n, d) {
    if (d < 0n) { n = -n; d = -d; }
    const g = gcdBig(n < 0n ? -n : n, d);
    return g > 1n ? { n: n / g, d: d / g } : { n: n, d: d };
  }
  function gcdBig(a, b) { while (b) { const t = a % b; a = b; b = t; } return a || 1n; }

  /** 整数方阵的核（假定一维），返回分量为互素正整数的向量；否则 null */
  function kernelVector(M) {
    const n = M.length;
    const R = M.map((r) => r.map((x) => fr(BigInt(x), 1n)));
    const sub = (a, b) => fr(a.n * b.d - b.n * a.d, a.d * b.d);
    const mul = (a, b) => fr(a.n * b.n, a.d * b.d);
    const div = (a, b) => fr(a.n * b.d, a.d * b.n);
    const pivots = [];
    let row = 0;
    for (let col = 0; col < n && row < n; col++) {
      let p = -1;
      for (let i = row; i < n; i++) if (R[i][col].n !== 0n) { p = i; break; }
      if (p < 0) continue;
      [R[row], R[p]] = [R[p], R[row]];
      const pv = R[row][col];
      for (let j = 0; j < n; j++) R[row][j] = div(R[row][j], pv);
      for (let i = 0; i < n; i++) {
        if (i === row || R[i][col].n === 0n) continue;
        const f = R[i][col];
        for (let j = 0; j < n; j++) R[i][j] = sub(R[i][j], mul(f, R[row][j]));
      }
      pivots.push(col);
      row++;
    }
    const free = [];
    for (let c = 0; c < n; c++) if (pivots.indexOf(c) < 0) free.push(c);
    if (free.length !== 1) return null;
    const f = free[0];
    const x = new Array(n).fill(null);
    x[f] = fr(1n, 1n);
    pivots.forEach((c, r) => { x[c] = fr(-R[r][f].n, R[r][f].d); });
    let L = 1n;
    x.forEach((v) => { L = L / gcdBig(L, v.d) * v.d; });
    let ints = x.map((v) => v.n * (L / v.d));
    let g = 0n;
    ints.forEach((v) => { g = gcdBig(g, v < 0n ? -v : v); });
    ints = ints.map((v) => v / g);
    if (ints.every((v) => v <= 0n)) ints = ints.map((v) => -v);
    if (!ints.every((v) => v > 0n)) return null;
    return ints.map(Number);
  }

  /**
   * 计算 Euclidean 连通分支 comp 的管。
   * @param A  整个箭图的箭头计数矩阵（无圈）
   * @param P  dim P(i)（= 路数矩阵 C 的第 i 行）
   * @return { delta, tubes: [{ rank, simples }], ok, reason }
   *   simples[k+1] = Φ(simples[k])，即 simples[k+1] = τ simples[k]
   */
  function tubes(A, P, comp, opts) {
    opts = opts || {};
    const n = A.length;
    const maxCand = opts.maxCandidates || 4e6;
    // Tits 型的对称矩阵 2I − (A + Aᵀ)，限制在分支上
    const S = comp.map((i) => comp.map((j) => (i === j ? 2 : 0) - A[i][j] - A[j][i]));
    const dc = kernelVector(S);
    if (!dc) return { ok: false, reason: 'no-delta' };
    const delta = new Array(n).fill(0);
    comp.forEach((v, t) => { delta[v] = dc[t]; });
    const euler = (x, y) => {
      let s = 0;
      for (let i = 0; i < n; i++) {
        if (!x[i]) continue;
        s += x[i] * y[i];
        for (let j = 0; j < n; j++) if (A[i][j]) s -= A[i][j] * x[i] * y[j];
      }
      return s;
    };
    const phi = (x) => {
      const y = new Array(n).fill(0); // y = Eᵀ x
      for (let j = 0; j < n; j++) {
        let s = x[j];
        for (let i = 0; i < n; i++) if (A[i][j]) s -= A[i][j] * x[i];
        y[j] = s;
      }
      const z = new Array(n).fill(0);
      for (let i = 0; i < n; i++) {
        let s = 0;
        for (let j = 0; j < n; j++) if (P[i][j] && y[j]) s += P[i][j] * y[j];
        z[i] = -s || 0;
      }
      return z;
    };
    let cand = 1;
    comp.forEach((v) => { cand *= delta[v] + 1; });
    if (cand > maxCand) return { ok: false, reason: 'too-large', delta: delta };

    // 枚举 0 < x < δ，q(x) = 1，∂(x) = 0
    const key = (x) => x.join(',');
    const roots = new Map();
    const x = new Array(n).fill(0);
    const rec = (t) => {
      if (t === comp.length) {
        if (x.every((v) => v === 0) || comp.every((v) => x[v] === delta[v])) return;
        if (euler(x, x) === 1 && euler(delta, x) === 0) roots.set(key(x), x.slice());
        return;
      }
      const v = comp[t];
      for (let a = 0; a <= delta[v]; a++) { x[v] = a; rec(t + 1); }
      x[v] = 0;
    };
    rec(0);

    // Φ 轨道
    const seen = new Set();
    const result = [];
    for (const [k, v] of roots) {
      if (seen.has(k)) continue;
      const orbit = [v];
      seen.add(k);
      let cur = phi(v);
      let guard = 0;
      while (key(cur) !== k && guard++ < 4 * n + 4) {
        orbit.push(cur);
        seen.add(key(cur));
        cur = phi(cur);
      }
      const sum = new Array(n).fill(0);
      orbit.forEach((o) => o.forEach((a, i) => { sum[i] += a; }));
      if (key(sum) === key(delta)) result.push({ rank: orbit.length, simples: orbit });
    }
    result.sort((a, b) => a.rank - b.rank);
    return { ok: true, delta: delta, tubes: result, phi: phi };
  }

  /** 管中模 M_k[l] 的维数向量：正则基座为 simples[k]，正则合成因子 simples[k], simples[k−1], … */
  function tubeModuleDim(tube, k, l) {
    const r = tube.simples.length;
    const n = tube.simples[0].length;
    const v = new Array(n).fill(0);
    for (let t = 0; t < l; t++) {
      const s = tube.simples[((k - t) % r + r) % r];
      for (let i = 0; i < n; i++) v[i] += s[i];
    }
    return v;
  }

  // ------------------------------------------------------------------ 导出范畴与丛范畴
  /*
   * Happel：D^b(mod kQ) 的 AR 箭图中含有投射模的分支是 ℤQ（Q 为 Dynkin 时就是整个 AR 箭图）。
   * 顶点 (r, i) 表示 τ^{-r}P(i)（r ∈ ℤ），箭头与 mod kQ 中相同：
   *   (r, j) → (r, i) 与 (r, i) → (r+1, j)，对每个箭头 i → j。
   * 在 K₀ 中，AR 三角 τX → E → X → τX[1] 给出 [τX] + [X] = [E]，
   * 所以可以用带符号的类“编织”，不在内射模处停止：τ⁻¹I(j) = P(j)[1]，τP(j) = I(j)[−1]。
   * 对象 M[d] 的类为 (−1)^d [M]；沿 τ 轨道每当类变号，平移次数 d 就加一（或减一）。
   *
   * 丛范畴 C_Q = D^b / ⟨F⟩，F = τ⁻¹[1]：
   *   Dynkin 型：不可分解对象 = 不可分解模 ∪ {P(i)[1]}，τ⁻¹(P(i)[1]) = P(i)（绕回）；
   *   其他类型：转移分支 (transjective) 为 ℤQ：… → τI → I → P[1] → P → τ⁻¹P → …，
   *            正则分支与 mod kQ 中相同（Euclidean 型为管）。
   */
  function signOf(v) {
    if (v.every((x) => x >= 0)) return 1;
    if (v.every((x) => x <= 0)) return -1;
    return 0;
  }

  /**
   * @param A    无圈箭图的箭头计数矩阵
   * @param opts {
   *   category: 'derived' | 'cluster',
   *   dmin, dmax : 导出范畴、Dynkin 型时显示的平移次数范围
   *   layers     : 非 Dynkin 型时 ℤQ 窗口向两侧各延伸的 τ 步数
   * }
   * @return {
   *   ok, reason, category, comps, P, I,
   *   nodes: [{ id, r, i, cls, deg, dim, comp, shiftP, ghost, proj, inj, simple, x, row }]
   *     cls 为 K₀ 中的类；dim 为模 M 的维数向量（对象为 M[deg]）；
   *     丛范畴中 shiftP ≥ 0 表示对象为 P(shiftP)[1]；ghost 表示绕回时重复画出的顶点
   *   edges, tau, total（丛范畴 Dynkin 型的不可分解对象个数）
   * }
   */
  function derivedQuiver(A, opts) {
    opts = opts || {};
    const n = A.length;
    const category = opts.category === 'cluster' ? 'cluster' : 'derived';
    const R = Math.max(1, Math.min(Math.floor(opts.layers || 4), 30));
    let dmin = Math.floor(opts.dmin != null ? opts.dmin : 0);
    let dmax = Math.floor(opts.dmax != null ? opts.dmax : 1);
    if (dmax < dmin) { const t = dmin; dmin = dmax; dmax = t; }
    if (dmax - dmin > 6) dmax = dmin + 6;
    if (!n) return { ok: false, reason: 'empty' };
    const order = topoOrder(A);
    if (!order) return { ok: false, reason: 'cyclic', cycle: findCycle(A) };
    const sinkFirst = order.slice().reverse();

    const base = arQuiver(A, { layers: R + 2 });
    const P = base.P, I = base.I;
    const comps = base.comps;
    const compOf = new Array(n);
    comps.forEach((c, ci) => c.verts.forEach((v) => { compOf[v] = ci; }));
    const dynkin = (i) => comps[compOf[i]].kind === 'dynkin';
    const key = (v) => v.join(',');
    const projIdx = new Map(P.map((v, j) => [key(v), j]));
    const injIdx = new Map(I.map((v, j) => [key(v), j]));

    // ---- 编织 ℤQ：cls.get(r)[i]，deg.get(r)[i]
    const cls = new Map(), deg = new Map();
    cls.set(0, P.map((v) => v.slice()));
    deg.set(0, new Array(n).fill(0));
    const forward = (r) => { // 由 r 计算 r+1
      const cur = cls.get(r), next = new Array(n);
      for (const i of sinkFirst) {
        const v = cur[i].map((t) => -t);
        for (let k = 0; k < n; k++) if (A[k][i] > 0) cur[k].forEach((x, t) => { v[t] += A[k][i] * x; });
        for (let j = 0; j < n; j++) if (A[i][j] > 0) next[j].forEach((x, t) => { v[t] += A[i][j] * x; });
        next[i] = v;
      }
      cls.set(r + 1, next);
      deg.set(r + 1, next.map((v, i) => deg.get(r)[i] + (signOf(v) !== signOf(cur[i]) ? 1 : 0)));
    };
    const backward = (r) => { // 由 r 计算 r−1
      const cur = cls.get(r), prev = new Array(n);
      for (const i of order) {
        const v = cur[i].map((t) => -t);
        for (let k = 0; k < n; k++) if (A[k][i] > 0) prev[k].forEach((x, t) => { v[t] += A[k][i] * x; });
        for (let j = 0; j < n; j++) if (A[i][j] > 0) cur[j].forEach((x, t) => { v[t] += A[i][j] * x; });
        prev[i] = v;
      }
      cls.set(r - 1, prev);
      deg.set(r - 1, prev.map((v, i) => deg.get(r)[i] - (signOf(v) !== signOf(cur[i]) ? 1 : 0)));
    };

    // 需要的 r 范围
    const anyDynkin = comps.some((c) => c.kind === 'dynkin');
    const anyInf = comps.some((c) => c.kind !== 'dynkin');
    let rLo = 0, rHi = 0;
    const GUARD = 2000;
    const needF = (d) => (category === 'derived' ? d <= dmax : d <= 1); // Dynkin：还需要向前编织
    const needB = (d) => category === 'derived' && d >= dmin;            // Dynkin：还需要向后编织
    while (rHi < GUARD) {
      const d = deg.get(rHi);
      const moreDyn = anyDynkin && d.some((x, i) => dynkin(i) && needF(x));
      const moreInf = anyInf && rHi < R;
      if (!moreDyn && !moreInf) break;
      forward(rHi);
      rHi++;
    }
    while (rLo > -GUARD) {
      const d = deg.get(rLo);
      const moreDyn = anyDynkin && d.some((x, i) => dynkin(i) && needB(x));
      const moreInf = anyInf && rLo > -(category === 'cluster' ? R + 2 : R + 1);
      if (!moreDyn && !moreInf) break;
      backward(rLo);
      rLo--;
    }

    // ---- 选出要画的顶点
    const nodes = [];
    const at = new Map();
    const isUnit = (v) => v.filter((x) => x !== 0).length === 1 && v.reduce((a, b) => a + b, 0) === 1;
    const add = (r, i, props) => {
      const c = cls.get(r)[i], d = deg.get(r)[i];
      const dim = d % 2 === 0 ? c.slice() : c.map((x) => -x || 0);
      const node = Object.assign({
        id: nodes.length, r: r, i: i, cls: c, deg: d, dim: dim, comp: compOf[i],
        shiftP: -1, ghost: false
      }, props || {});
      node.proj = node.shiftP < 0 && projIdx.has(key(node.dim)) ? projIdx.get(key(node.dim)) : -1;
      node.inj = node.shiftP < 0 && injIdx.has(key(node.dim)) ? injIdx.get(key(node.dim)) : -1;
      node.simple = node.shiftP < 0 && isUnit(node.dim);
      nodes.push(node);
      at.set(r + ':' + i, node.id);
      return node;
    };
    for (let r = rLo; r <= rHi; r++) {
      for (let i = 0; i < n; i++) {
        const d = deg.get(r)[i];
        if (dynkin(i)) {
          if (category === 'derived') {
            if (d >= dmin && d <= dmax) add(r, i);
          } else {
            if (d === 0) add(r, i);
            else if (d === 1 && projIdx.has(key(cls.get(r)[i].map((x) => -x || 0)))) {
              add(r, i, { shiftP: projIdx.get(key(cls.get(r)[i].map((x) => -x || 0))) });
            }
          }
        } else {
          if (category === 'derived') {
            if (r >= -R && r < R) add(r, i);
          } else if (r >= -R - 1 && r < R) {
            if (r >= 0) add(r, i);
            else if (r === -1) add(r, i, { shiftP: i, dimOverride: null });
            else {
              // (r, i) 在 C_Q 中是 τ^{|r|−2} I(i)，其维数向量为 −[ (r+1, i) ]
              const node = add(r, i);
              node.deg = 0;
              node.dim = cls.get(r + 1)[i].map((x) => -x || 0);
              node.proj = projIdx.has(key(node.dim)) ? projIdx.get(key(node.dim)) : -1;
              node.inj = injIdx.has(key(node.dim)) ? injIdx.get(key(node.dim)) : -1;
              node.simple = isUnit(node.dim);
            }
          }
        }
      }
    }
    // 丛范畴、Dynkin 型：在 P(j)[1] 的 τ⁻¹ 位置重复画出 P(j)（绕回），标为 ghost
    if (category === 'cluster') {
      nodes.slice().forEach((nd) => {
        if (nd.shiftP < 0 || !dynkin(nd.i)) return;
        if (!cls.has(nd.r + 1)) forward(nd.r);
        const g = add(nd.r + 1, nd.i, { ghost: true });
        g.deg = 0;
        g.dim = P[nd.shiftP].slice();
        g.proj = nd.shiftP;
        g.inj = injIdx.has(key(g.dim)) ? injIdx.get(key(g.dim)) : -1;
        g.simple = isUnit(g.dim);
      });
      nodes.forEach((nd) => { if (nd.shiftP >= 0) nd.dim = P[nd.shiftP].slice(); });
    }

    // ---- 箭头与 τ
    const edges = [], tau = [];
    nodes.forEach((b) => {
      const r = b.r, i = b.i;
      for (let j = 0; j < n; j++) {
        const m = A[i][j];
        if (!m) continue;
        const a1 = at.get(r + ':' + j);              // (r, j) → (r, i)
        if (a1 != null) edges.push({ from: a1, to: b.id, mult: m });
        const c1 = at.get((r + 1) + ':' + j);        // (r, i) → (r+1, j)
        if (c1 != null) edges.push({ from: b.id, to: c1, mult: m });
      }
      const t = at.get((r - 1) + ':' + i);
      if (t != null) tau.push({ from: b.id, to: t });
    });

    // ---- 布局
    let rowStart = 0;
    comps.forEach((comp, ci) => {
      const h = heights(A, comp.verts);
      const rows = rowOrder(A, comp.verts);
      const rowOf = new Map(rows.map((v, t) => [v, rowStart + t]));
      nodes.filter((nd) => nd.comp === ci).forEach((nd) => {
        nd.row = rowOf.get(nd.i);
        nd.x = nd.r * h.T + h.c.get(nd.i);
      });
      comp.rowStart = rowStart;
      comp.rows = rows.length;
      comp.gapX = null;
      rowStart += rows.length + 1;
    });

    const total = category === 'cluster' && comps.every((c) => c.kind === 'dynkin')
      ? nodes.filter((nd) => !nd.ghost).length : null;
    return {
      ok: true, category: category, comps: comps, P: P, I: I, layers: R, dmin: dmin, dmax: dmax,
      finite: total != null, nodes: nodes, edges: edges, tau: tau, total: total
    };
  }

  /**
   * Exact Hom / Ext¹ dimensions for indecomposable modules over a Dynkin
   * path algebra kQ, with k algebraically closed. This is NOT a computation
   * for a quotient kQ/I, a derived category, or a cluster category.
   *
   * Fix X and write h(Y) = dim Hom(X,Y). Applying Hom(X,-) to the almost
   * split sequence ending at a nonprojective Y gives
   *   h(Y) = Σ_{Z→Y} m(Z,Y) h(Z) − h(τY) + δ(X,Y).
   * The last term is the dimension of the simple functor at Y. For a
   * projective Y, rad Y → Y is right almost split and the same recurrence
   * holds without the τY term. Dynkin AR quivers are directed, so this
   * determines h in topological order (including the projective boundary).
   * Finally Ext¹(X,Y) = h(Y) − <dim X, dim Y> by heredity.
   *
   * All matrices are indexed [source node id][target node id] in `ar`.
   * `compatible[X][Y]` means Ext¹ vanishes in BOTH directions. Recurrence
   * data is returned for reproducible, numeric explanations in the UI:
   * predecessors[Y] = [{ from, mult }], tauOf[Y] = node id or null.
   * Unsupported input fails explicitly; it is never approximated by a
   * finite window of an infinite AR component.
   */
  function dynkinHomExt(A) {
    if (!Array.isArray(A)) return { ok: false, reason: 'invalid-matrix' };
    const n = A.length;
    if (!n) return { ok: false, reason: 'empty' };
    for (let i = 0; i < n; i++) {
      if (!Array.isArray(A[i]) || A[i].length !== n) return { ok: false, reason: 'invalid-matrix' };
      for (let j = 0; j < n; j++) {
        if (!Number.isSafeInteger(A[i][j]) || A[i][j] < 0) return { ok: false, reason: 'invalid-matrix' };
      }
    }
    // Bound the quadratic tables before knitting or allocating them.
    const maxObjects = 512;
    if (n > maxObjects) return { ok: false, reason: 'too-large', maxObjects: maxObjects };
    if (!topoOrder(A)) return { ok: false, reason: 'cyclic' };
    const comps = components(A).map((verts) => classify(A, verts));
    if (comps.some((c) => c.kind !== 'dynkin')) return { ok: false, reason: 'non-dynkin' };
    const count = comps.reduce((s, c) => s + c.count, 0);
    if (count > maxObjects) return { ok: false, reason: 'too-large', maxObjects: maxObjects, count: count };

    const ar = arQuiver(A, { tubes: false });
    if (!ar.ok || ar.nodes.length !== count) return { ok: false, reason: 'inconsistent-ar' };
    const size = ar.nodes.length;
    const predecessors = Array.from({ length: size }, () => []);
    const successors = Array.from({ length: size }, () => []);
    const indeg = new Array(size).fill(0);
    const tauOf = new Array(size).fill(null);
    ar.edges.forEach((edge) => {
      predecessors[edge.to].push({ from: edge.from, mult: edge.mult });
      successors[edge.from].push(edge.to);
      indeg[edge.to]++;
    });
    ar.tau.forEach((edge) => { tauOf[edge.from] = edge.to; });
    const order = [];
    for (let y = 0; y < size; y++) if (indeg[y] === 0) order.push(y);
    for (let pos = 0; pos < order.length; pos++) {
      successors[order[pos]].forEach((y) => { if (--indeg[y] === 0) order.push(y); });
    }
    if (order.length !== size) return { ok: false, reason: 'inconsistent-ar' };
    const position = new Array(size);
    order.forEach((y, p) => { position[y] = p; });
    if (ar.nodes.some((y) => (y.proj >= 0) !== (tauOf[y.id] === null) ||
      (tauOf[y.id] !== null && position[tauOf[y.id]] >= position[y.id]))) {
      return { ok: false, reason: 'inconsistent-ar' };
    }

    const matrix = () => Array.from({ length: size }, () => new Array(size).fill(0));
    const hom = matrix(), ext = matrix(), euler = matrix();
    // Precompute E dim Y for E = I − A; keep source supports sparse so
    // disconnected Dynkin components do not make Euler evaluation costly.
    const eulerTargets = ar.nodes.map((y) => y.dim.map((value, i) => {
      for (let j = 0; j < n; j++) if (A[i][j]) value -= A[i][j] * y.dim[j];
      return value;
    }));
    for (let x = 0; x < size; x++) {
      const support = [];
      ar.nodes[x].dim.forEach((value, i) => { if (value) support.push([i, value]); });
      for (const y of order) {
        let h = x === y ? 1 : 0;
        for (const p of predecessors[y]) h += p.mult * hom[x][p.from];
        if (tauOf[y] !== null) h -= hom[x][tauOf[y]];
        let pairing = 0;
        for (const [i, value] of support) pairing += value * eulerTargets[y][i];
        const e = h - pairing;
        // A failure here indicates an incomplete/invalid AR calculation,
        // not a negative dimension to be clamped to zero.
        if (!Number.isSafeInteger(h) || h < 0 || !Number.isSafeInteger(e) || e < 0) {
          return { ok: false, reason: 'inconsistent-ar' };
        }
        hom[x][y] = h;
        euler[x][y] = pairing;
        ext[x][y] = e;
      }
    }
    const compatible = ext.map((row, x) => row.map((e, y) => e === 0 && ext[y][x] === 0));
    return {
      ok: true, ar: ar, hom: hom, ext: ext, euler: euler,
      compatible: compatible, order: order, predecessors: predecessors, tauOf: tauOf
    };
  }

  const api = {
    dynkinHomExt: dynkinHomExt,
    components: components,
    topoOrder: topoOrder,
    findCycle: findCycle,
    kernelVector: kernelVector,
    tubes: tubes,
    tubeModuleDim: tubeModuleDim,
    derivedQuiver: derivedQuiver,
    classify: classify,
    titsForm: titsForm,
    arQuiver: arQuiver
  };
  if (typeof module !== 'undefined' && module.exports) module.exports = api;
  else root.ARCore = api;
})(typeof window !== 'undefined' ? window : this);
