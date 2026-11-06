/* app.js — 界面：绘制箭图 / 冰箭图，演示变异 */
(function () {
  'use strict';

  const Q = window.QuiverCore;
  const $ = (id) => document.getElementById(id);
  const NS = 'http://www.w3.org/2000/svg';
  const svg = $('canvas');
  const layerE = $('layer-edges');
  const layerT = $('layer-temp');
  const layerV = $('layer-vertices');

  const R = 19;          // 可变顶点半径
  const H = 17;          // 冰冻顶点（方框）半边长
  const GAP = 7;         // 平行箭头间距
  const MAX_PARALLEL = 4; // 超过此数量用数字标注
  const STORAGE_KEY = 'quiver-mutation-state-v1';

  // ---------------------------------------------------------------- 状态
  let state = { vertices: [], B: [], seq: [], seed: null };
  let undoStack = [];
  let redoStack = [];
  let mode = 'move';
  let selected = null;      // 选中顶点 id
  let pendingSource = null; // 点击式画箭头的起点 id
  let drag = null;          // 拖动顶点
  let arrowDrag = null;     // 拖动画箭头
  let demo = null;          // 分步演示 { stages, step, k }
  let playTimer = null;
  let modHL = null;         // 画布上显示维数向量的模 { kind: 'P'|'I'|'S', id }
  let paCache = { key: null, value: null };

  const MODE_HINTS = {
    move: '拖动顶点调整位置；双击顶点在该处变异；双击空白处添加顶点。',
    vertex: '点击空白处添加可变顶点（按住 Shift 添加冰冻顶点）。',
    frozenVertex: '点击空白处添加冰冻顶点（方框）。',
    arrow: '从起点拖到终点画一条箭头；也可以先点起点、再点终点。',
    freeze: '点击顶点在可变 / 冰冻之间切换。',
    delete: '点击箭头删除一条；点击顶点删除该顶点。',
    mutate: '点击可变顶点 k，进行变异 μₖ。'
  };

  // ---------------------------------------------------------------- 工具函数
  function el(tag, attrs, parent) {
    const e = document.createElementNS(NS, tag);
    for (const k in attrs) e.setAttribute(k, attrs[k]);
    if (parent) parent.appendChild(e);
    return e;
  }
  const idx = (id) => state.vertices.findIndex((v) => v.id === id);
  const byId = (id) => state.vertices.find((v) => v.id === id);
  const frozenArr = () => state.vertices.map((v) => !!v.frozen);
  const nextId = () => state.vertices.reduce((m, v) => Math.max(m, v.id), 0) + 1;

  function nextLabel() {
    const used = new Set(state.vertices.map((v) => v.label));
    let n = 1;
    while (used.has(String(n))) n++;
    return String(n);
  }

  function uniqueLabel(base) {
    const used = new Set(state.vertices.map((v) => v.label));
    if (!used.has(base)) return base;
    let n = 2;
    while (used.has(base + n)) n++;
    return base + n;
  }

  function canvasSize() {
    const r = svg.getBoundingClientRect();
    return { w: r.width || 800, h: r.height || 600 };
  }

  let toastTimer = null;
  function toast(msg) {
    const t = $('toast');
    t.textContent = msg;
    t.classList.add('show');
    clearTimeout(toastTimer);
    toastTimer = setTimeout(() => t.classList.remove('show'), 2400);
  }

  // ---------------------------------------------------------------- 撤销 / 重做
  function snapshot() {
    return JSON.stringify(state);
  }
  function restore(s) {
    state = JSON.parse(s);
    if (selected != null && !byId(selected)) selected = null;
    pendingSource = null;
  }
  function pushUndo() {
    undoStack.push(snapshot());
    if (undoStack.length > 300) undoStack.shift();
    redoStack = [];
  }
  function undo() {
    if (!undoStack.length) return;
    stopDemo();
    redoStack.push(snapshot());
    restore(undoStack.pop());
    render();
  }
  function redo() {
    if (!redoStack.length) return;
    stopDemo();
    undoStack.push(snapshot());
    restore(redoStack.pop());
    render();
  }

  /** 结构性修改（改变箭图本身）会清空变异记录 */
  function structural() {
    state.seq = [];
    state.seed = null;
    stopDemo();
  }

  // ---------------------------------------------------------------- 编辑操作
  function insertVertex(x, y, frozen, label) {
    const v = { id: nextId(), x: x, y: y, frozen: !!frozen, label: label || nextLabel() };
    state.vertices.push(v);
    state.B.forEach((row) => row.push(0));
    state.B.push(new Array(state.vertices.length).fill(0));
    return v;
  }

  function addVertex(x, y, frozen) {
    pushUndo();
    structural();
    const v = insertVertex(x, y, frozen);
    selected = v.id;
    render();
  }

  function removeVertexAt(i) {
    state.vertices.splice(i, 1);
    state.B.splice(i, 1);
    state.B.forEach((row) => row.splice(i, 1));
  }

  function deleteVertex(id) {
    const i = idx(id);
    if (i < 0) return;
    pushUndo();
    structural();
    removeVertexAt(i);
    if (selected === id) selected = null;
    render();
  }

  function addArrow(fromId, toId) {
    const i = idx(fromId), j = idx(toId);
    if (i < 0 || j < 0) return;
    if (i === j) { toast('箭图中不允许有自环（1-圈）。'); return; }
    const vi = state.vertices[i], vj = state.vertices[j];
    if (vi.frozen && vj.frozen) { toast('冰箭图中冰冻顶点之间不画箭头。'); return; }
    pushUndo();
    structural();
    state.B[i][j] += 1;
    state.B[j][i] -= 1;
    if (state.B[i][j] <= 0) toast('与反方向的箭头抵消了（箭图不含 2-圈）。');
    render();
  }

  function removeArrow(i, j) {
    if (!(state.B[i] && state.B[i][j] > 0)) return;
    pushUndo();
    structural();
    state.B[i][j] -= 1;
    state.B[j][i] += 1;
    render();
  }

  function setFrozen(id, val) {
    const i = idx(id);
    if (i < 0 || state.vertices[i].frozen === val) return;
    pushUndo();
    structural();
    state.vertices[i].frozen = val;
    if (val) {
      let removed = 0;
      state.vertices.forEach((w, j) => {
        if (j !== i && w.frozen && state.B[i][j] !== 0) {
          removed += Math.abs(state.B[i][j]);
          state.B[i][j] = 0;
          state.B[j][i] = 0;
        }
      });
      if (removed) toast('已删除冰冻顶点之间的 ' + removed + ' 条箭头。');
    }
    render();
  }

  function setEntry(i, j, v) {
    if (i === j) return;
    const fr = frozenArr();
    if (fr[i] && fr[j]) return;
    if (state.B[i][j] === v) return;
    pushUndo();
    structural();
    state.B[i][j] = v;
    state.B[j][i] = -v || 0;
    render();
  }

  function setLabel(id, label) {
    const v = byId(id);
    label = label.trim();
    if (!v || label === v.label) return;
    if (!label) { toast('标签不能为空。'); render(); return; }
    if (/[\s,，;]/.test(label)) { toast('标签不能包含空格或逗号。'); render(); return; }
    if (state.vertices.some((w) => w !== v && w.label === label)) { toast('标签「' + label + '」已被使用。'); render(); return; }
    pushUndo();
    v.label = label;
    render();
  }

  // ---------------------------------------------------------------- 变异
  function applyMutation(i) {
    const fr = frozenArr();
    if (!state.seq.length) state.seed = JSON.stringify(state.B);
    const stages = Q.mutationStages(state.B, i, fr);
    state.B = Q.mutate(state.B, i, fr);
    state.seq.push(state.vertices[i].id);
    return stages;
  }

  function mutateAt(id) {
    const i = idx(id);
    if (i < 0) return;
    if (state.vertices[i].frozen) { toast('不能在冰冻顶点处变异。'); return; }
    stopDemo();
    pushUndo();
    const stages = applyMutation(i);
    if ($('opt-steps').checked) {
      demo = { stages: stages, step: 0, k: id };
      render();
    } else {
      render();
      flash(id);
    }
  }

  function runSequence(text) {
    const tokens = text.split(/[\s,，;；]+/).map((t) => t.replace(/^(μ|mu)_?/i, '')).filter(Boolean);
    if (!tokens.length) { toast('请输入变异序列，例如：1 2 1'); return; }
    const ids = [];
    for (const t of tokens) {
      const v = state.vertices.find((w) => w.label === t);
      if (!v) { toast('找不到标签为「' + t + '」的顶点。'); return; }
      if (v.frozen) { toast('「' + t + '」是冰冻顶点，不能变异。'); return; }
      ids.push(v.id);
    }
    if (ids.length === 1) { mutateAt(ids[0]); return; }
    stopDemo();
    pushUndo();
    ids.forEach((id) => applyMutation(idx(id)));
    render();
    flash(ids[ids.length - 1]);
    toast('已执行 ' + ids.length + ' 次变异。');
  }

  function randomMutation() {
    const last = state.seq[state.seq.length - 1];
    let cand = state.vertices.filter((v) => !v.frozen && v.id !== last);
    if (!cand.length) cand = state.vertices.filter((v) => !v.frozen);
    if (!cand.length) { toast('没有可变顶点。'); return; }
    mutateAt(cand[Math.floor(Math.random() * cand.length)].id);
  }

  function backToSeed() {
    if (!state.seed) { toast('当前没有变异记录。'); return; }
    stopDemo();
    pushUndo();
    state.B = JSON.parse(state.seed);
    state.seq = [];
    state.seed = null;
    render();
    toast('已回到初始种子。');
  }

  function stopDemo() {
    demo = null;
    if (playTimer) { clearInterval(playTimer); playTimer = null; }
  }

  function flash(id) {
    const g = layerV.querySelector('[data-id="' + id + '"]');
    if (!g) return;
    g.classList.remove('flash');
    void g.getBBox();
    g.classList.add('flash');
  }

  // ---------------------------------------------------------------- 冰箭图工具
  function centroid() {
    const V = state.vertices;
    if (!V.length) { const s = canvasSize(); return { x: s.w / 2, y: s.h / 2 }; }
    return {
      x: V.reduce((a, v) => a + v.x, 0) / V.length,
      y: V.reduce((a, v) => a + v.y, 0) / V.length
    };
  }

  function addCoefficients(sign) {
    const mutable = state.vertices.filter((v) => !v.frozen);
    if (!mutable.length) { toast('没有可变顶点。'); return; }
    pushUndo();
    structural();
    const c = centroid();
    mutable.forEach((v) => {
      let dx = v.x - c.x, dy = v.y - c.y;
      let len = Math.hypot(dx, dy);
      if (len < 1) { dx = 0; dy = -1; len = 1; }
      const w = insertVertex(v.x + dx / len * 75, v.y + dy / len * 75, true, uniqueLabel(v.label + '′'));
      const i = idx(v.id), j = idx(w.id);
      state.B[i][j] = sign;
      state.B[j][i] = -sign;
    });
    render();
    toast(sign > 0 ? '已添加主系数：i → i′。' : '已添加对偶系数：i′ → i。');
  }

  function unfreezeAll() {
    if (!state.vertices.some((v) => v.frozen)) { toast('没有冰冻顶点。'); return; }
    pushUndo();
    structural();
    state.vertices.forEach((v) => { v.frozen = false; });
    render();
  }

  function removeFrozen() {
    if (!state.vertices.some((v) => v.frozen)) { toast('没有冰冻顶点。'); return; }
    pushUndo();
    structural();
    for (let i = state.vertices.length - 1; i >= 0; i--) {
      if (state.vertices[i].frozen) {
        if (state.vertices[i].id === selected) selected = null;
        removeVertexAt(i);
      }
    }
    render();
  }

  function circleLayout() {
    const V = state.vertices;
    if (!V.length) return;
    pushUndo();
    const s = canvasSize();
    const cx = s.w / 2, cy = s.h / 2;
    const mut = V.filter((v) => !v.frozen), frz = V.filter((v) => v.frozen);
    const r1 = Math.max(60, Math.min(s.w, s.h) * (frz.length ? 0.22 : 0.33));
    const r2 = Math.min(s.w, s.h) * 0.4;
    const place = (list, r, phase) => list.forEach((v, k) => {
      const a = -Math.PI / 2 + phase + 2 * Math.PI * k / list.length;
      v.x = cx + (list.length > 1 ? r * Math.cos(a) : 0);
      v.y = cy + (list.length > 1 ? r * Math.sin(a) : 0);
    });
    place(mut, r1, 0);
    place(frz, r2, frz.length ? Math.PI / frz.length : 0);
    render();
  }

  /** 把所有顶点缩放/平移到画布内（只缩小不放大）并居中 */
  function fitToView(record) {
    const V = state.vertices;
    if (!V.length) return false;
    const s = canvasSize();
    const pad = 40;
    const xs = V.map((v) => v.x), ys = V.map((v) => v.y);
    const minX = Math.min(...xs), maxX = Math.max(...xs), minY = Math.min(...ys), maxY = Math.max(...ys);
    const bw = maxX - minX, bh = maxY - minY;
    const k = Math.min(1, (s.w - 2 * pad) / (bw || 1), (s.h - 2 * pad) / (bh || 1));
    const cx = (minX + maxX) / 2, cy = (minY + maxY) / 2;
    const inside = minX >= pad / 2 && maxX <= s.w - pad / 2 && minY >= pad / 2 && maxY <= s.h - pad / 2;
    if (!record && inside) return false;
    if (record) pushUndo();
    V.forEach((v) => {
      v.x = s.w / 2 + (v.x - cx) * k;
      v.y = s.h / 2 + (v.y - cy) * k;
    });
    return true;
  }

  function clearAll() {
    if (!state.vertices.length) return;
    pushUndo();
    state = { vertices: [], B: [], seq: [], seed: null };
    selected = null;
    stopDemo();
    render();
  }

  // ---------------------------------------------------------------- 示例
  function polygonFan(n) {
    // n 边形以顶点 1 为扇心的三角剖分，对应 Gr(2,n) 的冰箭图
    const pts = [];
    for (let i = 1; i <= n; i++) {
      const a = -Math.PI / 2 - 2 * Math.PI * (i - 1) / n;
      pts[i] = [2.7 * Math.cos(a), 2.7 * Math.sin(a)];
    }
    const name = (a, b) => (a < b ? '' + a + b : '' + b + a);
    const verts = [], arrows = [];
    const mid = (a, b) => [(pts[a][0] + pts[b][0]) / 2, (pts[a][1] + pts[b][1]) / 2];
    for (let i = 1; i <= n; i++) {
      const j = i === n ? 1 : i + 1;
      const m = mid(i, j);
      verts.push([name(i, j), m[0] * 1.08, m[1] * 1.08, true]);
    }
    for (let j = 3; j < n; j++) {
      const m = mid(1, j);
      verts.push([name(1, j), m[0] * 0.75, m[1] * 0.75 + 0.35, false]);
    }
    const isFrozen = (s) => verts.find((v) => v[0] === s)[3];
    for (let a = 2; a < n; a++) {
      const b = a + 1;
      const s = [name(1, a), name(a, b), name(1, b)];
      for (let t = 0; t < 3; t++) {
        const p = s[t], q = s[(t + 1) % 3];
        if (!(isFrozen(p) && isFrozen(q))) arrows.push([p, q, 1]);
      }
    }
    return { verts: verts, arrows: arrows };
  }

  const PRESETS = {
    A3: { verts: [['1', -2, -0.5], ['2', 0, 0.7], ['3', 2, -0.5]], arrows: [['1', '2', 1], ['2', '3', 1]] },
    A4: { verts: [['1', -3, -0.5], ['2', -1, 0.6], ['3', 1, -0.5], ['4', 3, 0.6]], arrows: [['1', '2', 1], ['3', '2', 1], ['3', '4', 1]] },
    D4: { verts: [['1', -1.8, -1.2], ['2', 0, 0], ['3', 1.8, -1.2], ['4', 0, 2]], arrows: [['1', '2', 1], ['3', '2', 1], ['4', '2', 1]] },
    E6: {
      verts: [['1', -2.6, 0.6], ['2', -1.3, 0.6], ['3', 0, 0.6], ['4', 1.3, 0.6], ['5', 2.6, 0.6], ['6', 0, -0.9]],
      arrows: [['1', '2', 1], ['2', '3', 1], ['4', '3', 1], ['5', '4', 1], ['6', '3', 1]]
    },
    A2tilde: { verts: [['1', -1.8, 1], ['2', 0, -1.6], ['3', 1.8, 1]], arrows: [['1', '2', 1], ['2', '3', 1], ['1', '3', 1]] },
    cyc3: { verts: [['1', -1.7, 1], ['2', 0, -1.9], ['3', 1.7, 1]], arrows: [['1', '2', 1], ['2', '3', 1], ['3', '1', 1]] },
    kronecker: { verts: [['1', -1.5, 0], ['2', 1.5, 0]], arrows: [['1', '2', 2]] },
    markov: { verts: [['1', -1.9, 1.1], ['2', 0, -2.1], ['3', 1.9, 1.1]], arrows: [['1', '2', 2], ['2', '3', 2], ['3', '1', 2]] },
    A2prin: {
      verts: [['1', -1.4, 0.9], ['2', 1.4, 0.9], ['1′', -1.4, -1.3, true], ['2′', 1.4, -1.3, true]],
      arrows: [['1', '2', 1], ['1', '1′', 1], ['2', '2′', 1]]
    },
    A3prin: {
      verts: [['1', -2.2, 0.5], ['2', 0, 1.5], ['3', 2.2, 0.5], ['1′', -2.2, -1.5, true], ['2′', 0, -0.6, true], ['3′', 2.2, -1.5, true]],
      arrows: [['1', '2', 1], ['2', '3', 1], ['1', '1′', 1], ['2', '2′', 1], ['3', '3′', 1]]
    },
    gr25: polygonFan(5),
    gr26: polygonFan(6),
    empty: { verts: [], arrows: [] }
  };

  function buildPreset(p) {
    const s = canvasSize();
    const unit = Math.max(45, Math.min(105, Math.min(s.w, s.h) / 6.5));
    const cx = s.w / 2, cy = s.h / 2;
    const vertices = p.verts.map((v, k) => ({ id: k + 1, label: v[0], x: cx + v[1] * unit, y: cy + v[2] * unit, frozen: !!v[3] }));
    const n = vertices.length;
    const B = Q.zeros(n);
    const li = (l) => vertices.findIndex((v) => v.label === l);
    p.arrows.forEach(([a, b, c]) => {
      const i = li(a), j = li(b);
      B[i][j] += c;
      B[j][i] -= c;
    });
    return { vertices: vertices, B: B, seq: [], seed: null };
  }

  function loadPreset(name) {
    const p = PRESETS[name];
    if (!p) return;
    pushUndo();
    stopDemo();
    state = buildPreset(p);
    selected = null;
    pendingSource = null;
    render();
  }


  // ---------------------------------------------------------------- 路代数
  const SUP = '⁰¹²³⁴⁵⁶⁷⁸⁹';
  const sup = (x) => String(x).split('').map((d) => SUP[+d]).join('');
  const fmt = (x) => (x === null ? '∞' : x.toString());

  function paOptions() {
    const trunc = $('pa-rel').value === 'trunc';
    let L = parseInt($('pa-L').value, 10);
    if (!(L >= 1)) L = 2;
    return { trunc: trunc, L: Math.min(L, 30), mutableOnly: $('pa-mutable').checked };
  }

  /** 当前箭图的路代数（带缓存）。verts 为参与计算的顶点下标（显示顺序：先可变后冰冻）*/
  function computePA() {
    const o = paOptions();
    const V = state.vertices;
    const key = JSON.stringify([state.B, V.map((v) => v.frozen), o]);
    if (paCache.key === key) return paCache.value;
    const mut = [], frz = [];
    V.forEach((v, i) => (v.frozen ? frz : mut).push(i));
    const verts = o.mutableOnly ? mut : mut.concat(frz);
    const A = verts.map((i) => verts.map((j) => Math.max(state.B[i][j], 0)));
    const pa = Q.pathAlgebra(A, o.trunc ? { truncate: o.L } : {});
    const value = { pa: pa, verts: verts, opts: o };
    paCache = { key: key, value: value };
    return value;
  }

  /** 模的维数向量，按 verts 的顺序 */
  function moduleDims(info, kind, a) {
    if (kind === 'P') return Q.projectiveDim(info.pa, a);
    if (kind === 'I') return Q.injectiveDim(info.pa, a);
    return info.verts.map((_, j) => (j === a ? 1n : 0n));
  }

  function modName(kind, label) {
    return kind + '(' + label + ')';
  }

  function layerText(vec, info) {
    const parts = [];
    vec.forEach((m, j) => {
      if (m > 0n) parts.push(state.vertices[info.verts[j]].label + (m > 1n ? sup(m) : ''));
    });
    return parts.length ? parts.join(' ⊕ ') : '0';
  }

  function renderPathAlgebra() {
    const V = state.vertices;
    const info = computePA();
    const pa = info.pa, o = info.opts;
    $('pa-L').hidden = $('pa-L-label').hidden = !o.trunc;
    const algName = o.trunc ? 'kQ / R' + sup(o.L) : 'kQ';
    const nArrows = pa.powers.length > 1 ? Q.totalDim(pa.powers[1].flat()) : 0n;

    // 概要
    let html = '';
    if (!info.verts.length) {
      html = '<span class="hint">没有顶点。</span>';
    } else {
      html += '<div>dim ' + algName + ' = <span class="big">' + fmt(pa.dim) + '</span></div>';
      if (!pa.acyclic) {
        const cyc = pa.onCycle.map((a) => V[info.verts[a]].label).join(', ');
        html += '<div class="' + (o.trunc ? 'hint' : 'warn') + '">Q 含有向圈（经过顶点 ' + cyc + '）' +
          (o.trunc ? '。' : '，kQ 是无穷维的；可选择「截断」。') + '</div>';
      }
      html += '<dl>' +
        '<dt>顶点 / 箭头</dt><dd>' + info.verts.length + ' / ' + nArrows + '</dd>' +
        '<dt>有向圈</dt><dd>' + (pa.acyclic ? '无（Q 无圈）' : '有') + '</dd>' +
        '<dt>Loewy 长度</dt><dd>' + (pa.loewy != null ? pa.loewy : '∞') + '</dd>' +
        (pa.finite && pa.loewy ? '<dt>最长非零路</dt><dd>' + (pa.loewy - 1) + '</dd>' : '') +
        '</dl>';
    }
    $('pa-summary').innerHTML = html;

    // 维数向量表
    const kind = $('pa-kind').value;
    const esc = (t) => t.replace(/[&<>"]/g, (ch) => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' }[ch]));
    if (modHL && (idx(modHL.id) < 0 || info.verts.indexOf(idx(modHL.id)) < 0)) modHL = null;
    let t = '';
    if (info.verts.length) {
      t += '<thead><tr><th>模</th>' + info.verts.map((i) => '<th class="' + (V[i].frozen ? 'frozen' : '') + '">' + esc(V[i].label) + '</th>').join('') + '<th>dim</th></tr></thead><tbody>';
      const totals = info.verts.map(() => 0n);
      let totalsInf = info.verts.map(() => false);
      info.verts.forEach((i, a) => {
        const d = moduleDims(info, kind, a);
        const active = modHL && modHL.kind === kind && modHL.id === V[i].id;
        t += '<tr data-id="' + V[i].id + '" class="' + (active ? 'active' : '') + '"><th>' + esc(modName(kind, V[i].label)) + '</th>';
        d.forEach((x, j) => {
          if (x === null) totalsInf[j] = true; else totals[j] += x;
          t += '<td class="' + (x === null ? 'inf' : x === 0n ? 'zero' : '') + '">' + fmt(x) + '</td>';
        });
        t += '<td class="tot' + (Q.totalDim(d) === null ? ' inf' : '') + '">' + fmt(Q.totalDim(d)) + '</td></tr>';
      });
      t += '</tbody>';
      if (kind !== 'S') {
        const all = totals.map((x, j) => (totalsInf[j] ? null : x));
        t += '<tfoot><tr><td>Σ</td>' + all.map((x) => '<td>' + fmt(x) + '</td>').join('') + '<td class="tot">' + fmt(pa.dim) + '</td></tr></tfoot>';
      }
    }
    $('pa-table').innerHTML = t;

    renderARSummary();

    // 根层 / 基座层
    const box = $('pa-layers');
    box.innerHTML = '';
    if (modHL && modHL.kind !== 'S') {
      const a = info.verts.indexOf(idx(modHL.id));
      const label = byId(modHL.id).label;
      const ls = Q.layers(pa, a, modHL.kind);
      const isP = modHL.kind === 'P';
      const title = document.createElement('div');
      title.className = 'title';
      title.textContent = modName(modHL.kind, label) + (isP ? ' 的根层（自顶向下）' : ' 的基座层（自下向上）');
      box.appendChild(title);
      const lw = document.createElement('div');
      lw.className = 'loewy';
      const rows = ls.map((vec, l) => ({ name: (isP ? (l === 0 ? '顶' : 'rad' + sup(l)) : (l === 0 ? '基座' : 'soc' + sup(l + 1))), text: layerText(vec, info) }));
      if (!pa.finite) rows.push({ name: '…', text: '（无穷多层）' });
      (isP ? rows : rows.slice().reverse()).forEach((r) => {
        const row = document.createElement('div');
        row.className = 'layer';
        const n = document.createElement('span'); n.className = 'lname'; n.textContent = r.name;
        const v = document.createElement('span'); v.className = 'lval'; v.textContent = r.text;
        row.append(n, v);
        lw.appendChild(row);
      });
      box.appendChild(lw);
      const hint = document.createElement('p');
      hint.className = 'hint';
      hint.textContent = isP
        ? '第 l 层 = 从 ' + label + ' 出发、长度为 l 的路的终点。'
        : '自下第 l 层 = 长度为 l、终点为 ' + label + ' 的路的起点。';
      box.appendChild(hint);
    }
  }

  // ---------------------------------------------------------------- AR 箭图
  const AR = window.ARCore;
  let arScale = null;   // null = 适应窗口
  let arSel = null;     // 选中的 AR 顶点 id
  let arCache = { key: null, value: null };

  function arLayers() {
    const L = parseInt($('ar-layers').value, 10);
    return Math.max(1, Math.min(12, L >= 1 ? L : 4));
  }

  function computeAR() {
    const info = computePA();
    const layers = arLayers();
    const key = JSON.stringify([state.B, info.verts, layers]);
    if (arCache.key === key) return arCache.value;
    const A = info.verts.map((i) => info.verts.map((j) => Math.max(state.B[i][j], 0)));
    const ar = info.verts.length ? AR.arQuiver(A, { layers: layers }) : { ok: false, reason: 'empty' };
    const value = { ar: ar, info: info };
    arCache = { key: key, value: value };
    return value;
  }

  const vlabel = (info, a) => state.vertices[info.verts[a]].label;

  function arNodeName(nd, info) {
    const l = vlabel(info, nd.i);
    if (nd.kind === 'P') return nd.r === 0 ? 'P' + l : 'τ⁻' + sup(nd.r) + 'P' + l;
    return nd.r === 0 ? 'I' + l : 'τ' + (nd.r === 1 ? '' : sup(nd.r)) + 'I' + l;
  }

  function dimLabel(dim) {
    return dim.length <= 12 && dim.every((x) => x < 10) ? dim.join('') : dim.join(',');
  }

  function arSummary(value) {
    const ar = value.ar, info = value.info;
    if (!ar.ok) {
      if (ar.reason === 'empty') return '没有顶点。';
      const esc = (t) => t.replace(/[&<>"]/g, (ch) => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' }[ch]));
      const cyc = (ar.cycle || []).map((a) => vlabel(info, a));
      const cycText = cyc.length ? '（例如 ' + esc(cyc.concat(cyc[0]).join(' → ')) + '）' : '';
      return '<span class="ar-warn">当前箭图含有向圈' + cycText + '，kQ 是无穷维的，无法计算 AR 箭图。</span>' +
        '目前只支持无圈箭图的路代数。';
    }
    const kindName = { dynkin: '', euclidean: ' Euclidean', wild: '' };
    const names = ar.comps.map((c) => c.name + kindName[c.kind]).join(' ⊔ ');
    let html;
    if (ar.finite) {
      html = '有限表示型（' + names + '），共 <b>' + ar.total + '</b> 个不可分解模（与正根一一对应）。';
    } else {
      html = '无限表示型（' + names + '）。画出预投射、预内射分支的前 ' + ar.layers + ' 层，规则分支未画出。';
    }
    if (info.opts.trunc) html += ' 注：按无关系的 kQ 计算，不考虑截断。';
    return html;
  }

  function renderARSummary() {
    const value = computeAR();
    $('ar-summary').innerHTML = arSummary(value);
    $('btn-ar').disabled = false;
    $('btn-ar').textContent = value.ar.ok ? '查看 AR 箭图' : '查看 AR 箭图（当前不可计算）';
  }

  /** 箭图有圈时，给出可以得到无圈箭图的操作 */
  function arFixes(value) {
    const box = $('ar-info');
    box.innerHTML = '';
    if (value.ar.reason !== 'cyclic') return;
    box.append('可以试试：');
    const add = (text, fn) => {
      const b = document.createElement('button');
      b.type = 'button';
      b.textContent = text;
      b.className = 'ar-fix';
      b.addEventListener('click', () => { fn(); arSel = null; arScale = null; drawAR(); });
      box.append(b);
    };
    const info = value.info;
    if (!info.opts.mutableOnly && state.vertices.some((v) => v.frozen)) {
      const mut = [];
      state.vertices.forEach((v, i) => { if (!v.frozen) mut.push(i); });
      const A = mut.map((i) => mut.map((j) => Math.max(state.B[i][j], 0)));
      if (mut.length && AR.topoOrder(A)) add('只用可变部分（可变部分无圈）', () => { $('pa-mutable').checked = true; render(); });
    }
    if (state.seed) add('回到初始种子', backToSeed);
    if (undoStack.length) add('撤销上一步', undo);
    add('打开示例 A₃', () => loadPreset('A3'));
    const p = document.createElement('p');
    p.className = 'hint';
    p.textContent = '变异常常会产生有向圈；箭图无圈时（例如 Dynkin 型箭图的某些定向）才能计算 AR 箭图。';
    box.append(p);
  }

  function openAR() {
    arSel = null;
    arScale = null;
    $('dlg-ar').showModal();
    drawAR();
  }

  function drawAR() {
    const value = computeAR();
    const ar = value.ar, info = value.info;
    const eE = $('ar-edges'), eN = $('ar-nodes'), svgAR = $('ar-canvas');
    eE.textContent = '';
    eN.textContent = '';
    $('ar-desc').innerHTML = arSummary(value);
    $('ar-layers-wrap').hidden = !ar.ok || ar.finite;
    $('ar-order').textContent = ar.ok ? '维数向量分量顺序：(' + info.verts.map((i) => state.vertices[i].label).join(', ') + ')' : '';
    document.querySelectorAll('.ar-controls, #ar-scroll, .ar-legend').forEach((x) => { x.hidden = !ar.ok; });
    $('dlg-ar').classList.toggle('compact', !ar.ok);
    if (!ar.ok) {
      svgAR.setAttribute('width', 0);
      svgAR.setAttribute('height', 0);
      arFixes(value);
      return;
    }
    const nodes = ar.nodes;
    if (arSel != null && !nodes[arSel]) arSel = null;
    const mode = $('ar-label').value;
    const text = (nd) => (mode === 'name' ? arNodeName(nd, info) : dimLabel(nd.dim));
    const widths = nodes.map((nd) => Math.max(26, text(nd).length * 7.4 + 12));
    const maxW = Math.max.apply(null, widths);
    const UX = Math.max(26, (maxW + 12) / 2), UY = 46, PAD = 34, HH = 11;
    const multi = ar.comps.length > 1;
    const minX = Math.min.apply(null, nodes.map((nd) => nd.x));
    const maxX = Math.max.apply(null, nodes.map((nd) => nd.x));
    const maxRow = Math.max.apply(null, nodes.map((nd) => nd.row));
    const left = PAD + maxW / 2 + (multi ? 40 : 0);
    const pos = (nd) => ({ X: left + (nd.x - minX) * UX, Y: PAD + nd.row * UY });
    const W = left + (maxX - minX) * UX + PAD + maxW / 2;
    const H = PAD * 2 + maxRow * UY;

    // 邻居
    const nb = new Set();
    if (arSel != null) {
      ar.edges.forEach((e) => {
        if (e.from === arSel) nb.add(e.to);
        if (e.to === arSel) nb.add(e.from);
      });
    }

    const trim = (w, dx, dy) => Math.min(Math.abs(dx) > 1e-9 ? w / Math.abs(dx) : Infinity, Math.abs(dy) > 1e-9 ? (HH + 3) / Math.abs(dy) : Infinity);

    // τ（虚线）
    if ($('ar-tau').checked) {
      ar.tau.forEach((t) => {
        const a = nodes[t.from], b = nodes[t.to];
        const p = pos(a), q = pos(b);
        el('line', { x1: p.X - widths[a.id] / 2 - 3, y1: p.Y, x2: q.X + widths[b.id] / 2 + 3, y2: q.Y, class: 'ar-tau' }, eE);
      });
    }

    // 不可约映射
    ar.edges.forEach((e) => {
      const a = nodes[e.from], b = nodes[e.to];
      const p = pos(a), q = pos(b);
      const hl = arSel != null && (e.from === arSel || e.to === arSel);
      const dx = q.X - p.X, dy = q.Y - p.Y, len = Math.hypot(dx, dy);
      const nx = -dy / len, ny = dx / len;
      const bend = Math.abs(a.row - b.row) >= 2 ? 0.22 * len : 0;
      const m = e.mult <= 3 ? e.mult : 1;
      for (let t = 0; t < m; t++) {
        const off = (t - (m - 1) / 2) * 5;
        const P1 = { x: p.X + nx * off, y: p.Y + ny * off }, P2 = { x: q.X + nx * off, y: q.Y + ny * off };
        const C = { x: (p.X + q.X) / 2 + nx * (bend + off), y: (p.Y + q.Y) / 2 + ny * (bend + off) };
        let d1x = C.x - P1.x, d1y = C.y - P1.y, l1 = Math.hypot(d1x, d1y); d1x /= l1; d1y /= l1;
        let d2x = C.x - P2.x, d2y = C.y - P2.y, l2 = Math.hypot(d2x, d2y); d2x /= l2; d2y /= l2;
        const t1 = trim(widths[a.id] / 2 + 3, d1x, d1y), t2 = trim(widths[b.id] / 2 + 5, d2x, d2y);
        const S = { x: P1.x + d1x * t1, y: P1.y + d1y * t1 }, E = { x: P2.x + d2x * t2, y: P2.y + d2y * t2 };
        const d = bend ? 'M' + S.x + ',' + S.y + ' Q' + C.x + ',' + C.y + ' ' + E.x + ',' + E.y : 'M' + S.x + ',' + S.y + ' L' + E.x + ',' + E.y;
        el('path', { d: d, class: 'ar-edge' + (hl ? ' hl' : '') + (e.mult > 3 ? ' thick' : ''), 'marker-end': 'url(#' + (hl ? 'ar-ah-hl' : 'ar-ah') + ')' }, eE);
      }
      if (e.mult > 3) {
        const cx = (p.X + q.X) / 2 + nx * bend * 0.5, cy = (p.Y + q.Y) / 2 + ny * bend * 0.5;
        el('circle', { cx: cx, cy: cy, r: 9, class: 'edge-label-bg' }, eE);
        el('text', { x: cx, y: cy, class: 'edge-label' }, eE).textContent = String(e.mult);
      }
    });

    // 分支名称与规则分支的位置
    ar.comps.forEach((c) => {
      const yMid = PAD + (c.rowStart + (c.rows - 1) / 2) * UY;
      if (multi) el('text', { x: 8, y: yMid, class: 'ar-comp', 'dominant-baseline': 'central' }, eN).textContent = c.name;
      if (c.gapX != null) {
        el('text', { x: left + (c.gapX - minX) * UX, y: yMid, class: 'ar-gap' }, eN).textContent = '⋯ 规则分支 ⋯';
      }
    });

    // 模
    nodes.forEach((nd) => {
      const p = pos(nd);
      let cls = 'ar-node';
      if (nd.proj >= 0) cls += ' proj';
      if (nd.inj >= 0) cls += ' inj';
      if (nd.simple) cls += ' simple';
      if (nd.id === arSel) cls += ' sel';
      else if (nb.has(nd.id)) cls += ' nb';
      const g = el('g', { class: cls, transform: 'translate(' + p.X + ',' + p.Y + ')', 'data-ar': nd.id }, eN);
      el('title', {}, g).textContent = arNodeName(nd, info) + '  dim = (' + nd.dim.join(', ') + ')';
      el('rect', { x: -widths[nd.id] / 2, y: -HH, width: widths[nd.id], height: 2 * HH, rx: 5 }, g);
      el('text', {}, g).textContent = text(nd);
    });

    // 缩放
    const box = $('ar-scroll');
    if (arScale == null) {
      const fit = Math.min((box.clientWidth - 6) / W, (box.clientHeight - 6) / H);
      arScale = Math.max(0.3, Math.min(1.4, isFinite(fit) && fit > 0 ? fit : 1));
    }
    svgAR.setAttribute('viewBox', '0 0 ' + W + ' ' + H);
    svgAR.setAttribute('width', Math.round(W * arScale));
    svgAR.setAttribute('height', Math.round(H * arScale));

    renderARInfo(value);
  }

  function renderARInfo(value) {
    const ar = value.ar, info = value.info;
    const box = $('ar-info');
    if (arSel == null) {
      box.textContent = '点击一个模查看详情，同时高亮它的直接前驱与后继。共 ' + ar.nodes.length + ' 个模（图中）。';
      return;
    }
    const nd = ar.nodes[arSel];
    const parts = [arNodeName(nd, info)];
    if ((nd.kind === 'I' || nd.r > 0) && nd.proj >= 0) parts.push('P' + vlabel(info, nd.proj));
    if ((nd.kind === 'P' || nd.r > 0) && nd.inj >= 0) parts.push('I' + vlabel(info, nd.inj));
    if (nd.simple) parts.push('S' + vlabel(info, nd.dim.indexOf(1)));
    const preds = ar.edges.filter((e) => e.to === nd.id).map((e) => arNodeName(ar.nodes[e.from], info) + (e.mult > 1 ? sup(e.mult) : ''));
    const succs = ar.edges.filter((e) => e.from === nd.id).map((e) => arNodeName(ar.nodes[e.to], info) + (e.mult > 1 ? sup(e.mult) : ''));
    const total = nd.dim.reduce((a, b) => a + b, 0);
    box.innerHTML = '';
    const b = document.createElement('b');
    b.textContent = parts.join(' ≅ ');
    box.append(b, '　dim = ');
    const code = document.createElement('code');
    code.textContent = '(' + nd.dim.join(', ') + ')';
    box.append(code, '，总维数 ' + total + '，所在分支 ' + ar.comps[nd.comp].name);
    box.append(document.createElement('br'));
    box.append('直接前驱：' + (preds.join('，') || '无') + '；直接后继：' + (succs.join('，') || '无'));
  }

  /** 画布上要标注的维数：Map(vertex id → BigInt | null) */
  function highlightDims() {
    if (!modHL || demo) return null;
    const info = computePA();
    const a = info.verts.indexOf(idx(modHL.id));
    if (a < 0) return null;
    const d = moduleDims(info, modHL.kind, a);
    const m = new Map();
    info.verts.forEach((i, j) => m.set(state.vertices[i].id, d[j]));
    return m;
  }

  // ---------------------------------------------------------------- 绘制
  function trimDist(v, ux, uy) {
    return v.frozen ? H / Math.max(Math.abs(ux), Math.abs(uy)) : R;
  }

  function drawEdges(view) {
    layerE.textContent = '';
    const V = state.vertices;
    const A = view.A, hl = view.hl;
    const n = V.length;
    for (let i = 0; i < n; i++) {
      for (let j = 0; j < n; j++) {
        if (i === j || !A[i] || !(A[i][j] > 0)) continue;
        const c = A[i][j];
        const h = hl ? hl[i][j] : 0;
        const two = A[j][i] > 0;
        const a = V[i], b = V[j];
        const dx = b.x - a.x, dy = b.y - a.y;
        const len = Math.hypot(dx, dy);
        const ux = dx / len, uy = dy / len;
        const nx = -uy, ny = ux;
        const t1 = trimDist(a, ux, uy) + 1.5;
        const t2 = trimDist(b, ux, uy) + 2;
        if (!(len > t1 + t2 + 6)) continue;
        const g = el('g', { class: 'edge-group', 'data-i': i, 'data-j': j }, layerE);
        const drawn = c <= MAX_PARALLEL ? c : 1;
        const base = two ? ((drawn - 1) * GAP / 2 + 6) : 0;
        for (let t = 0; t < drawn; t++) {
          const off = base + (t - (drawn - 1) / 2) * GAP;
          const color = (c <= MAX_PARALLEL ? t < h : h > 0) ? view.color : null;
          el('line', {
            x1: a.x + ux * t1 + nx * off, y1: a.y + uy * t1 + ny * off,
            x2: b.x - ux * t2 + nx * off, y2: b.y - uy * t2 + ny * off,
            class: 'edge' + (color ? ' ' + color : '') + (c > MAX_PARALLEL ? ' thick' : ''),
            'marker-end': 'url(#ah-' + (color || 'base') + ')'
          }, g);
        }
        if (c > MAX_PARALLEL) {
          const mx = (a.x + b.x) / 2 + nx * base, my = (a.y + b.y) / 2 + ny * base;
          const color = h > 0 ? view.color : '';
          el('circle', { cx: mx, cy: my, r: 11, class: 'edge-label-bg ' + color }, g);
          const tx = el('text', { x: mx, y: my, class: 'edge-label' }, g);
          tx.textContent = String(c);
        }
        if (!demo) {
          el('line', {
            x1: a.x + nx * base, y1: a.y + ny * base, x2: b.x + nx * base, y2: b.y + ny * base,
            class: 'edge-hit'
          }, g);
        }
      }
    }
  }

  function drawVertices() {
    layerV.textContent = '';
    const dims = highlightDims();
    state.vertices.forEach((v) => {
      let cls = 'vertex' + (v.frozen ? ' frozen' : '');
      const dv = dims ? dims.get(v.id) : undefined;
      if (dims && (dv === undefined || dv === 0n)) cls += ' dim0';
      if (dims && v.id === modHL.id) cls += ' dimtarget';
      if (v.id === selected) cls += ' selected';
      if (v.id === pendingSource || (arrowDrag && arrowDrag.from === v.id)) cls += ' source';
      if (demo && v.id === demo.k) cls += ' mutating';
      const g = el('g', { class: cls, transform: 'translate(' + v.x + ',' + v.y + ')', 'data-id': v.id }, layerV);
      el('circle', { r: R, class: 'halo' }, g);
      if (v.frozen) el('rect', { x: -H, y: -H, width: 2 * H, height: 2 * H, rx: 3, class: 'shape' }, g);
      else el('circle', { r: R, class: 'shape' }, g);
      const t = el('text', {}, g);
      t.textContent = v.label;
      if (v.label.length > 2) t.setAttribute('font-size', v.label.length > 3 ? '9' : '11');
      if (dims && dv !== undefined && dv !== 0n) {
        const b = el('text', { x: R - 2, y: -R - 2, class: 'dimbadge' + (dv === null ? ' inf' : '') }, g);
        b.textContent = fmt(dv);
      }
    });
  }

  function renderCanvas() {
    const view = demo ? demo.stages[demo.step] : { A: Q.toCounts(state.B), hl: null, color: 'none' };
    drawEdges(view);
    drawVertices();
  }

  function renderMatrix() {
    const V = state.vertices;
    const table = $('matrix');
    const full = $('opt-full').checked;
    if (!V.length) {
      table.innerHTML = '<tr><td class="matrix-empty">（空箭图）</td></tr>';
      $('matrix-caption').textContent = '';
      return;
    }
    const mut = [], frz = [];
    V.forEach((v, i) => (v.frozen ? frz : mut).push(i));
    const rows = mut.concat(frz);
    const cols = full ? rows : mut;
    $('matrix-caption').textContent = full
      ? '完整斜对称矩阵（' + V.length + '×' + V.length + '），先列可变顶点，再列冰冻顶点。'
      : '扩展交换矩阵 B̃（' + rows.length + '×' + cols.length + '）：行 = 全部顶点，列 = 可变顶点；冰冻顶点所在行为系数部分。';
    const esc = (s) => s.replace(/[&<>"]/g, (ch) => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' }[ch]));
    let html = '<tr><th></th>' + cols.map((c) => '<th class="' + (V[c].frozen ? 'frozen' : '') + '">' + esc(V[c].label) + '</th>').join('') + '</tr>';
    rows.forEach((r, ri) => {
      const sep = ri === mut.length && mut.length > 0 ? ' sep' : '';
      html += '<tr><th class="' + (V[r].frozen ? 'frozen' : '') + '">' + esc(V[r].label) + '</th>';
      cols.forEach((c) => {
        const val = state.B[r][c];
        const dis = r === c || (V[r].frozen && V[c].frozen);
        const cls = val > 0 ? 'pos' : val < 0 ? 'neg' : '';
        html += '<td class="' + (V[r].frozen ? 'frozen-row' : '') + sep + '"><input type="number" step="1" value="' + val + '" data-r="' + r + '" data-c="' + c + '" class="' + cls + '"' + (dis ? ' disabled' : '') + ' aria-label="b ' + esc(V[r].label) + ',' + esc(V[c].label) + '"></td>';
      });
      html += '</tr>';
    });
    if (!cols.length) html += '<tr><td class="matrix-empty" colspan="2">没有可变顶点</td></tr>';
    table.innerHTML = html;
  }

  function renderStats() {
    const V = state.vertices;
    let arrows = 0, maxMult = 0;
    state.B.forEach((row) => row.forEach((x) => { if (x > 0) { arrows += x; maxMult = Math.max(maxMult, x); } }));
    const nm = V.filter((v) => !v.frozen).length;
    const items = [
      ['顶点', V.length],
      ['可变顶点', nm],
      ['冰冻顶点', V.length - nm],
      ['箭头', arrows],
      ['最大重数', maxMult],
      ['变异次数', state.seq.length]
    ];
    $('stats').innerHTML = items.map(([k, v]) => '<dt>' + k + '</dt><dd>' + v + '</dd>').join('');
  }

  function renderSeq() {
    const log = $('seq-log');
    if (!state.seq.length) {
      log.textContent = '尚未变异。';
      return;
    }
    const labels = state.seq.map((id) => { const v = byId(id); return v ? v.label : '?'; });
    log.innerHTML = '';
    log.append('已执行：');
    labels.forEach((l, k) => {
      const b = document.createElement('b');
      b.textContent = 'μ' + l;
      log.append(b);
      if (k < labels.length - 1) log.append(' → ');
    });
  }

  function renderSelection() {
    const sec = $('sel-section');
    const v = selected != null ? byId(selected) : null;
    sec.hidden = !v;
    if (!v) return;
    if (document.activeElement !== $('sel-label')) $('sel-label').value = v.label;
    $('sel-frozen').checked = !!v.frozen;
    $('sel-mutate').disabled = !!v.frozen;
  }

  function renderStageBar() {
    const bar = $('stage-bar');
    bar.hidden = !demo;
    if (!demo) return;
    const st = demo.stages[demo.step];
    const v = byId(demo.k);
    const k = v ? v.label : 'k';
    $('stage-title').textContent = st.title.replace('μ_k', 'μ' + k);
    $('stage-desc').textContent = st.text.replace(/\bk\b/g, k);
    $('stage-count').textContent = (demo.step + 1) + ' / ' + demo.stages.length;
    $('stage-prev').disabled = demo.step === 0;
    $('stage-next').disabled = demo.step === demo.stages.length - 1;
    $('stage-play').textContent = playTimer ? '暂停' : '自动播放';
  }

  function renderTools() {
    document.querySelectorAll('.tool').forEach((b) => {
      const on = b.dataset.mode === mode;
      b.classList.toggle('active', on);
      b.setAttribute('aria-checked', on ? 'true' : 'false');
      b.setAttribute('role', 'radio');
    });
    $('mode-hint').textContent = MODE_HINTS[mode];
    document.body.className = 'mode-' + mode;
  }

  function render() {
    renderCanvas();
    renderMatrix();
    renderStats();
    renderPathAlgebra();
    renderSeq();
    renderSelection();
    renderStageBar();
    renderTools();
    $('empty-hint').hidden = state.vertices.length > 0;
    $('btn-undo').disabled = !undoStack.length;
    $('btn-redo').disabled = !redoStack.length;
    $('btn-seed').disabled = !state.seed;
    save();
  }

  function save() {
    try { localStorage.setItem(STORAGE_KEY, snapshot()); } catch (e) { /* 忽略 */ }
  }

  function load() {
    try {
      const s = localStorage.getItem(STORAGE_KEY);
      if (!s) return false;
      const o = JSON.parse(s);
      if (!validState(o)) return false;
      state = o;
      return true;
    } catch (e) {
      return false;
    }
  }

  function validState(o) {
    if (!o || !Array.isArray(o.vertices) || !Array.isArray(o.B)) return false;
    const n = o.vertices.length;
    if (o.B.length !== n || o.B.some((r) => !Array.isArray(r) || r.length !== n || r.some((x) => !Number.isInteger(x)))) return false;
    if (!Q.isSkewSymmetric(o.B)) return false;
    if (o.vertices.some((v) => typeof v.id !== 'number' || typeof v.label !== 'string' || !isFinite(v.x) || !isFinite(v.y))) return false;
    if (!Array.isArray(o.seq)) o.seq = [];
    if (typeof o.seed !== 'string') o.seed = null;
    return true;
  }

  // ---------------------------------------------------------------- 指针交互
  function svgPoint(e) {
    const r = svg.getBoundingClientRect();
    return { x: e.clientX - r.left, y: e.clientY - r.top };
  }

  function vertexAt(p) {
    const V = state.vertices;
    for (let k = V.length - 1; k >= 0; k--) {
      const v = V[k];
      if (v.frozen ? (Math.abs(p.x - v.x) <= H + 3 && Math.abs(p.y - v.y) <= H + 3) : Math.hypot(p.x - v.x, p.y - v.y) <= R + 3) return v;
    }
    return null;
  }

  svg.addEventListener('pointerdown', (e) => {
    if (e.button !== 0) return;
    const p = svgPoint(e);
    const v = vertexAt(p);
    const edgeG = e.target.closest ? e.target.closest('.edge-group') : null;

    switch (mode) {
      case 'move':
      case 'vertex':
      case 'frozenVertex':
        if (v) {
          selected = v.id;
          drag = { id: v.id, ox: p.x - v.x, oy: p.y - v.y, sx: p.x, sy: p.y, moved: false };
          svg.setPointerCapture(e.pointerId);
          render();
        } else if (mode === 'move') {
          if (selected != null) { selected = null; render(); }
        } else {
          addVertex(p.x, p.y, mode === 'frozenVertex' || e.shiftKey);
        }
        break;
      case 'arrow':
        if (v) {
          if (pendingSource != null && pendingSource !== v.id) {
            const from = pendingSource;
            pendingSource = null;
            addArrow(from, v.id);
          } else {
            arrowDrag = { from: v.id, sx: p.x, sy: p.y, moved: false };
            svg.setPointerCapture(e.pointerId);
            render();
          }
        } else if (pendingSource != null) {
          pendingSource = null;
          render();
        }
        break;
      case 'freeze':
        if (v) setFrozen(v.id, !v.frozen);
        break;
      case 'delete':
        if (v) deleteVertex(v.id);
        else if (edgeG) removeArrow(+edgeG.dataset.i, +edgeG.dataset.j);
        break;
      case 'mutate':
        if (v) mutateAt(v.id);
        break;
    }
  });

  svg.addEventListener('pointermove', (e) => {
    const p = svgPoint(e);
    if (drag) {
      if (!drag.moved) {
        if (Math.hypot(p.x - drag.sx, p.y - drag.sy) < 3) return;
        pushUndo();
        drag.moved = true;
      }
      const v = byId(drag.id);
      if (!v) return;
      const s = canvasSize();
      v.x = Math.max(R, Math.min(s.w - R, p.x - drag.ox));
      v.y = Math.max(R, Math.min(s.h - R, p.y - drag.oy));
      renderCanvas();
    } else if (arrowDrag) {
      if (!arrowDrag.moved && Math.hypot(p.x - arrowDrag.sx, p.y - arrowDrag.sy) < 4) return;
      arrowDrag.moved = true;
      const a = byId(arrowDrag.from);
      const target = vertexAt(p);
      let ex = p.x, ey = p.y;
      if (target && target.id !== a.id) {
        const d = Math.hypot(target.x - a.x, target.y - a.y) || 1;
        const ux = (target.x - a.x) / d, uy = (target.y - a.y) / d;
        const t = trimDist(target, ux, uy) + 2;
        ex = target.x - ux * t;
        ey = target.y - uy * t;
      }
      layerT.textContent = '';
      el('line', { x1: a.x, y1: a.y, x2: ex, y2: ey, class: 'edge temp', 'marker-end': 'url(#ah-temp)' }, layerT);
    }
  });

  function endPointer(e) {
    if (drag) {
      const moved = drag.moved;
      drag = null;
      if (moved) render();
    }
    if (arrowDrag) {
      const ad = arrowDrag;
      arrowDrag = null;
      layerT.textContent = '';
      const target = e.type === 'pointerup' ? vertexAt(svgPoint(e)) : null;
      if (target && target.id !== ad.from) {
        addArrow(ad.from, target.id);
      } else if (!ad.moved) {
        pendingSource = ad.from; // 点击式：等待终点
        render();
      } else {
        render();
      }
    }
  }
  svg.addEventListener('pointerup', endPointer);
  svg.addEventListener('pointercancel', endPointer);

  svg.addEventListener('dblclick', (e) => {
    const p = svgPoint(e);
    const v = vertexAt(p);
    if (v) {
      if (mode === 'move') mutateAt(v.id);
    } else if (mode === 'move' || mode === 'arrow' || mode === 'freeze') {
      addVertex(p.x, p.y, e.shiftKey);
    }
  });

  // ---------------------------------------------------------------- 控件
  function setMode(m) {
    mode = m;
    pendingSource = null;
    render();
  }

  document.querySelectorAll('.tool').forEach((b) => b.addEventListener('click', () => setMode(b.dataset.mode)));
  $('btn-undo').addEventListener('click', undo);
  $('btn-redo').addEventListener('click', redo);
  $('btn-help').addEventListener('click', () => $('dlg-help').showModal());
  $('btn-io').addEventListener('click', () => { $('io-text').value = exportJSON(); $('dlg-io').showModal(); });

  $('btn-seq').addEventListener('click', () => runSequence($('seq-input').value));
  $('seq-input').addEventListener('keydown', (e) => { if (e.key === 'Enter') runSequence($('seq-input').value); });
  $('btn-random').addEventListener('click', randomMutation);
  $('btn-seed').addEventListener('click', backToSeed);
  $('opt-steps').addEventListener('change', () => {
    try { localStorage.setItem(STORAGE_KEY + '-steps', $('opt-steps').checked ? '1' : '0'); } catch (e) { /* 忽略 */ }
  });

  $('btn-principal').addEventListener('click', () => addCoefficients(1));
  $('btn-coprincipal').addEventListener('click', () => addCoefficients(-1));
  $('btn-unfreeze').addEventListener('click', unfreezeAll);
  $('btn-remove-frozen').addEventListener('click', removeFrozen);

  $('preset').addEventListener('change', (e) => {
    if (e.target.value) loadPreset(e.target.value);
    e.target.value = '';
  });
  $('btn-layout').addEventListener('click', circleLayout);
  $('btn-fit').addEventListener('click', () => { if (fitToView(true)) render(); });
  let resizeTimer = null;
  window.addEventListener('resize', () => {
    clearTimeout(resizeTimer);
    resizeTimer = setTimeout(() => { if (fitToView(false)) render(); }, 150);
  });
  $('btn-clear').addEventListener('click', clearAll);

  $('opt-full').addEventListener('change', renderMatrix);

  // 路代数面板
  ['pa-rel', 'pa-mutable', 'pa-kind'].forEach((id) => $(id).addEventListener('change', () => {
    if (id === 'pa-kind' && modHL) modHL = { kind: $('pa-kind').value, id: modHL.id };
    render();
  }));
  $('pa-L').addEventListener('input', () => { if (parseInt($('pa-L').value, 10) >= 1) render(); });
  $('btn-ar').addEventListener('click', openAR);
  ['ar-label', 'ar-tau'].forEach((id) => $(id).addEventListener('change', drawAR));
  $('ar-layers').addEventListener('input', () => {
    if (parseInt($('ar-layers').value, 10) >= 1) { arSel = null; arScale = null; drawAR(); renderARSummary(); }
  });
  $('ar-zoom-in').addEventListener('click', () => { arScale = Math.min(4, (arScale || 1) * 1.25); drawAR(); });
  $('ar-zoom-out').addEventListener('click', () => { arScale = Math.max(0.15, (arScale || 1) / 1.25); drawAR(); });
  $('ar-zoom-fit').addEventListener('click', () => { arScale = null; drawAR(); });
  $('ar-nodes').addEventListener('click', (e) => {
    const g = e.target.closest('[data-ar]');
    if (!g) return;
    const id = +g.dataset.ar;
    arSel = arSel === id ? null : id;
    drawAR();
  });
  $('pa-table').addEventListener('click', (e) => {
    const tr = e.target.closest('tbody tr');
    if (!tr) return;
    const id = +tr.dataset.id;
    const kind = $('pa-kind').value;
    modHL = modHL && modHL.id === id && modHL.kind === kind ? null : { kind: kind, id: id };
    render();
  });
  $('matrix').addEventListener('change', (e) => {
    const t = e.target;
    if (!t.dataset || t.dataset.r == null) return;
    const v = Number(t.value);
    if (!Number.isInteger(v) || Math.abs(v) > 99) { toast('请输入 −99 到 99 之间的整数。'); renderMatrix(); return; }
    setEntry(+t.dataset.r, +t.dataset.c, v);
  });

  $('sel-label').addEventListener('change', (e) => setLabel(selected, e.target.value));
  $('sel-label').addEventListener('keydown', (e) => { if (e.key === 'Enter') e.target.blur(); });
  $('sel-frozen').addEventListener('change', (e) => setFrozen(selected, e.target.checked));
  $('sel-mutate').addEventListener('click', () => mutateAt(selected));
  $('sel-delete').addEventListener('click', () => deleteVertex(selected));

  // 分步演示
  function stageGo(d) {
    if (!demo) return;
    demo.step = Math.max(0, Math.min(demo.stages.length - 1, demo.step + d));
    if (demo.step === demo.stages.length - 1 && playTimer) { clearInterval(playTimer); playTimer = null; }
    renderCanvas();
    renderStageBar();
  }
  $('stage-prev').addEventListener('click', () => stageGo(-1));
  $('stage-next').addEventListener('click', () => stageGo(1));
  $('stage-close').addEventListener('click', () => { stopDemo(); render(); });
  $('stage-play').addEventListener('click', () => {
    if (!demo) return;
    if (playTimer) {
      clearInterval(playTimer);
      playTimer = null;
    } else {
      if (demo.step === demo.stages.length - 1) demo.step = 0;
      renderCanvas();
      playTimer = setInterval(() => stageGo(1), 1500);
    }
    renderStageBar();
  });

  // 键盘
  document.addEventListener('keydown', (e) => {
    const tag = (e.target.tagName || '').toLowerCase();
    if (tag === 'input' || tag === 'textarea' || tag === 'select') return;
    if (document.querySelector('dialog[open]')) return;
    const key = e.key.toLowerCase();
    if ((e.ctrlKey || e.metaKey) && key === 'z') { e.preventDefault(); if (e.shiftKey) redo(); else undo(); return; }
    if ((e.ctrlKey || e.metaKey) && key === 'y') { e.preventDefault(); redo(); return; }
    if (e.ctrlKey || e.metaKey || e.altKey) return;
    if (demo && (e.key === 'ArrowLeft' || e.key === 'ArrowRight')) { e.preventDefault(); stageGo(e.key === 'ArrowLeft' ? -1 : 1); return; }
    const modes = { s: 'move', v: 'vertex', i: 'frozenVertex', a: 'arrow', f: 'freeze', d: 'delete', m: 'mutate' };
    if (modes[key]) { setMode(modes[key]); return; }
    if ((e.key === 'Delete' || e.key === 'Backspace') && selected != null) { e.preventDefault(); deleteVertex(selected); return; }
    if (e.key === 'Escape') {
      modHL = null;
      pendingSource = null;
      selected = null;
      stopDemo();
      render();
    }
  });

  // ---------------------------------------------------------------- 导入 / 导出
  function exportJSON() {
    const V = state.vertices;
    const vs = V.map((v) => '    ' + JSON.stringify({ label: v.label, x: Math.round(v.x), y: Math.round(v.y), frozen: !!v.frozen }));
    const ms = state.B.map((r) => '    ' + JSON.stringify(r));
    return '{\n  "format": "quiver-mutation",\n  "version": 1,\n  "vertices": [\n' + vs.join(',\n') + '\n  ],\n  "matrix": [\n' + ms.join(',\n') + '\n  ]\n}\n';
  }

  function exportMatrix() {
    const V = state.vertices;
    const fr = [];
    V.forEach((v, i) => { if (v.frozen) fr.push(i + 1); });
    const width = Math.max(2, ...state.B.flat().map((x) => String(x).length)) + 1;
    let s = '# 顶点顺序: ' + V.map((v) => v.label).join(' ') + '\n';
    if (fr.length) s += 'frozen: ' + fr.join(' ') + '\n';
    s += state.B.map((r) => r.map((x) => String(x).padStart(width)).join('')).join('\n') + '\n';
    return s;
  }

  function exportTikZ() {
    const V = state.vertices;
    const tex = (l) => l.replace(/′/g, "'").replace(/([#%&_{}$^])/g, '\\$1');
    const c = centroid();
    const f = (x) => { const s = (x / 60).toFixed(2); return s === '-0.00' ? '0.00' : s; };
    let s = '% \\usetikzlibrary{arrows.meta}\n\\begin{tikzpicture}[>={Stealth[length=2mm]},\n' +
      '  mut/.style={circle,draw,minimum size=6mm,inner sep=1pt},\n' +
      '  frz/.style={rectangle,draw,minimum size=6mm,inner sep=1pt,fill=blue!8}]\n';
    V.forEach((v, i) => {
      s += '  \\node[' + (v.frozen ? 'frz' : 'mut') + '] (v' + (i + 1) + ') at (' + f(v.x - c.x) + ',' + f(c.y - v.y) + ') {$' + tex(v.label) + '$};\n';
    });
    const bends = { 1: [null], 2: [8, -8], 3: [12, null, -12], 4: [15, 5, -5, -15] };
    for (let i = 0; i < V.length; i++) {
      for (let j = 0; j < V.length; j++) {
        const c = state.B[i][j];
        if (c <= 0) continue;
        const a = 'v' + (i + 1), b = 'v' + (j + 1);
        if (bends[c]) {
          bends[c].forEach((bd) => {
            s += '  \\draw[->] (' + a + ') to' + (bd == null ? '' : '[bend left=' + bd + ']') + ' (' + b + ');\n';
          });
        } else {
          s += '  \\draw[->,thick] (' + a + ') to node[midway,fill=white,inner sep=1pt]{\\small $' + c + '$} (' + b + ');\n';
        }
      }
    }
    return s + '\\end{tikzpicture}\n';
  }

  function importText(text) {
    text = text.trim();
    if (!text) { toast('内容为空。'); return false; }
    let next = null;
    if (text[0] === '{') {
      let o;
      try { o = JSON.parse(text); } catch (e) { toast('JSON 解析失败：' + e.message); return false; }
      if (!Array.isArray(o.vertices) || !Array.isArray(o.matrix)) { toast('JSON 缺少 vertices 或 matrix。'); return false; }
      const s = canvasSize();
      const n = o.vertices.length;
      const vertices = o.vertices.map((v, k) => ({
        id: k + 1,
        label: String(v.label != null ? v.label : k + 1),
        x: isFinite(v.x) ? +v.x : s.w / 2 + 150 * Math.cos(2 * Math.PI * k / n),
        y: isFinite(v.y) ? +v.y : s.h / 2 + 150 * Math.sin(2 * Math.PI * k / n),
        frozen: !!v.frozen
      }));
      next = { vertices: vertices, B: o.matrix, seq: [], seed: null };
    } else {
      const lines = text.split(/\r?\n/).map((l) => l.trim()).filter((l) => l && l[0] !== '#' && l[0] !== '%');
      let frozen = [];
      const rows = [];
      for (const l of lines) {
        const m = l.match(/^frozen\s*[:：]\s*(.*)$/i);
        if (m) { frozen = m[1].split(/[\s,，]+/).filter(Boolean).map(Number); continue; }
        rows.push(l.replace(/[[\]]/g, ' ').split(/[\s,，;]+/).filter(Boolean).map(Number));
      }
      const n = rows.length;
      const s = canvasSize();
      const r = Math.min(s.w, s.h) * 0.33;
      const vertices = rows.map((_, k) => ({
        id: k + 1,
        label: String(k + 1),
        x: s.w / 2 + (n > 1 ? r * Math.cos(-Math.PI / 2 + 2 * Math.PI * k / n) : 0),
        y: s.h / 2 + (n > 1 ? r * Math.sin(-Math.PI / 2 + 2 * Math.PI * k / n) : 0),
        frozen: frozen.includes(k + 1)
      }));
      next = { vertices: vertices, B: rows, seq: [], seed: null };
    }
    const n = next.vertices.length;
    if (next.B.length !== n || next.B.some((r) => !Array.isArray(r) || r.length !== n || r.some((x) => !Number.isInteger(x)))) {
      toast('矩阵必须是 ' + n + '×' + n + ' 的整数方阵。');
      return false;
    }
    if (new Set(next.vertices.map((v) => v.label)).size !== n) { toast('顶点标签有重复。'); return false; }
    if (!Q.isSkewSymmetric(next.B)) { toast('矩阵不是斜对称的（需要 b_ij = −b_ji）。'); return false; }
    let removed = 0;
    for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) {
      if (i !== j && next.vertices[i].frozen && next.vertices[j].frozen && next.B[i][j] !== 0) {
        if (next.B[i][j] > 0) removed += next.B[i][j];
        next.B[i][j] = 0;
      }
    }
    pushUndo();
    stopDemo();
    state = next;
    selected = null;
    render();
    toast(removed ? '已导入（忽略了冰冻顶点之间的 ' + removed + ' 条箭头）。' : '已导入。');
    return true;
  }

  $('io-json').addEventListener('click', () => { $('io-text').value = exportJSON(); });
  $('io-tikz').addEventListener('click', () => { $('io-text').value = exportTikZ(); });
  $('io-matrix').addEventListener('click', () => { $('io-text').value = exportMatrix(); });
  $('io-copy').addEventListener('click', () => {
    const ta = $('io-text');
    const done = () => toast('已复制到剪贴板。');
    if (navigator.clipboard && navigator.clipboard.writeText) {
      navigator.clipboard.writeText(ta.value).then(done, () => { ta.select(); document.execCommand('copy'); done(); });
    } else {
      ta.select();
      document.execCommand('copy');
      done();
    }
  });
  $('io-import').addEventListener('click', () => {
    if (importText($('io-text').value)) $('dlg-io').close();
  });

  // ---------------------------------------------------------------- 启动
  try { $('opt-steps').checked = localStorage.getItem(STORAGE_KEY + '-steps') !== '0'; } catch (e) { $('opt-steps').checked = true; }
  if (!load()) state = buildPreset(PRESETS.A3prin);
  fitToView(false);
  render();

  // 供调试 / 测试使用
  window.QuiverApp = {
    get state() { return state; },
    loadPreset: loadPreset,
    mutateAt: mutateAt,
    runSequence: runSequence,
    importText: importText,
    computePA: computePA,
    computeAR: computeAR,
    exportTikZ: exportTikZ
  };
})();
