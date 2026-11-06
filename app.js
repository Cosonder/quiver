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
    move: 'Drag vertices to move them; double-click a vertex to mutate there; double-click an empty spot to add a vertex.',
    vertex: 'Click an empty spot to add a mutable vertex (hold Shift for a frozen vertex).',
    frozenVertex: 'Click an empty spot to add a frozen vertex (square).',
    arrow: 'Drag from the source to the target to draw an arrow, or click the source and then the target.',
    freeze: 'Click a vertex to toggle between mutable and frozen.',
    delete: 'Click an arrow to remove one arrow; click a vertex to delete it.',
    mutate: 'Click a mutable vertex k to apply the mutation μₖ.'
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


  // ---------------------------------------------------------------- 证明（Proof）面板：LaTeX 排版
  // 证明以 LaTeX 源码书写：文本中 $…$ 为行内公式，$$…$$ 为行间公式，**…** 为粗体，*…* 为斜体；
  // 公式由 KaTeX 排版，正文使用 KaTeX_Main（Computer Modern）字体，与标准 LaTeX 文档一致。
  const PROOF_MAX = 80;
  let proofEntries = [];
  const LB = (i) => state.vertices[i].label;
  const texEsc = (t) => String(t).replace(/′/g, "'").replace(/([#$%&_{}])/g, '\\$1');
  const T = (i) => texEsc(LB(i));
  /** 两个下标：都是单个字符时直接相连，否则用逗号隔开 */
  const sub2 = (a, b) => (a.length === 1 && b.length === 1 ? a + b : a + ',' + b);
  const bij = (i, j) => 'b_{' + sub2(T(i), T(j)) + '}';
  const par = (x) => (x < 0 ? '(' + x + ')' : String(x));
  /** 若干个 TeX 片段（各自已带 $…$）用逗号连接，过多时省略 */
  const listT = (arr, max) => {
    max = max || 8;
    return arr.length > max ? arr.slice(0, max).join(', ') + ', … (' + arr.length + ' in total)' : arr.join(', ');
  };
  const arrowText = (i, j, m) => '$' + T(i) + '\\to ' + T(j) + (m > 1 ? '\\ (\\times ' + m + ')' : '') + '$';
  /** 向量的 TeX：(1,1,0)；全为非正时写成 −(…) */
  function texVec(v) {
    if (v.every((x) => x <= 0) && v.some((x) => x < 0)) return '-' + texVec(v.map((x) => -x));
    return '(' + v.join(',') + ')';
  }
  /** 底图类型的 TeX：A₃ → A_{3}，D̃₄ → \tilde{D}_{4} */
  function texType(name) {
    if (name === 'wild') return '\\text{wild}';
    const chars = Array.from(name);
    let letter = chars[0], rest = chars.slice(1), tilde = false;
    if (letter === 'Ã') { letter = 'A'; tilde = true; }
    if (letter === 'Ẽ') { letter = 'E'; tilde = true; }
    if (rest[0] === '̃') { tilde = true; rest = rest.slice(1); }
    const num = rest.map((c) => '₀₁₂₃₄₅₆₇₈₉'.indexOf(c)).join('');
    return (tilde ? '\\tilde{' + letter + '}' : letter) + '_{' + num + '}';
  }

  /**
   * 记录一条证明。opts.proof：是否以 “Proof.” 开头；opts.qed：是否以 □ 结尾。
   */
  function proof(title, lines, opts) {
    opts = opts || {};
    proofEntries.push({ title: title, lines: (lines || []).filter(Boolean), proof: !!opts.proof, qed: !!opts.qed });
    if (proofEntries.length > PROOF_MAX) proofEntries.shift();
    renderProof();
  }

  function renderMath(el, tex, display) {
    if (window.katex) {
      try {
        window.katex.render(tex, el, { displayMode: display, throwOnError: false, output: 'html' });
        return;
      } catch (e) { /* 退回纯文本 */ }
    }
    el.textContent = tex;
    el.classList.add('tex-fallback');
  }

  /** 把一段 LaTeX 风格的源码渲染到 parent 中 */
  function texToNodes(parent, src) {
    String(src).split(/(\$\$[\s\S]+?\$\$|\$[^$]+\$)/).forEach((part) => {
      if (!part) return;
      if (part.startsWith('$$')) {
        const d = document.createElement('div');
        d.className = 'pdisplay';
        renderMath(d, part.slice(2, -2), true);
        parent.appendChild(d);
      } else if (part.startsWith('$')) {
        const sp = document.createElement('span');
        renderMath(sp, part.slice(1, -1), false);
        parent.appendChild(sp);
      } else {
        part.split(/(\*\*[^*]+\*\*|\*[^*\s][^*]*\*)/).forEach((t) => {
          if (!t) return;
          if (t.startsWith('**')) { const b = document.createElement('b'); b.textContent = t.slice(2, -2); parent.appendChild(b); }
          else if (t.length > 2 && t.startsWith('*') && t.endsWith('*')) { const i = document.createElement('i'); i.textContent = t.slice(1, -1); parent.appendChild(i); }
          else parent.appendChild(document.createTextNode(t));
        });
      }
    });
  }

  /** 把证明条目画进一个 <ol>（amsthm 风格：粗体标题，斜体 Proof.，结尾 □） */
  function renderProofList(list, entries, emptyText) {
    list.textContent = '';
    if (!entries.length) {
      const li = document.createElement('li');
      li.className = 'proof-empty';
      li.textContent = emptyText;
      list.appendChild(li);
      return;
    }
    entries.forEach((e, n) => {
      const li = document.createElement('li');
      const t = document.createElement('div');
      t.className = 'ptitle';
      const num = document.createElement('span');
      num.className = 'pnum';
      num.textContent = (n + 1) + '.';
      t.appendChild(num);
      t.appendChild(document.createTextNode(' '));
      texToNodes(t, e.title);
      li.appendChild(t);
      e.lines.forEach((l, k) => {
        const para = document.createElement('div');
        para.className = 'ppara';
        if (k === 0 && e.proof) {
          const it = document.createElement('i');
          it.textContent = 'Proof.';
          para.append(it, ' ');
        }
        texToNodes(para, l);
        if (k === e.lines.length - 1 && e.qed) {
          const q = document.createElement('span');
          q.className = 'qed';
          renderMath(q, '\\square', false);
          para.appendChild(q);
        }
        li.appendChild(para);
      });
      list.appendChild(li);
    });
  }

  function renderProof() {
    const list = $('proof-list');
    renderProofList(list, proofEntries, 'Each step you take (drawing, editing, mutating) is explained here.');
    list.scrollTop = list.scrollHeight;
  }

  /** μ_k 的证明：先按三步组合描述，再用矩阵公式逐项核对 */
  function mutationProof(Bold, Bnew, k, fr, stages) {
    const n = Bold.length;
    const K = T(k);
    const pos = (x) => Math.max(x, 0);
    const paths = [];
    for (let i = 0; i < n; i++) {
      for (let j = 0; j < n; j++) {
        if (i === k || j === k || i === j) continue;
        const m = pos(Bold[i][k]) * pos(Bold[k][j]);
        if (m > 0) paths.push('$' + T(i) + '\\to ' + K + '\\to ' + T(j) + (m > 1 ? '\\ (\\times ' + m + ')' : '') + '$');
      }
    }
    const inc = [];
    for (let j = 0; j < n; j++) {
      if (Bold[j][k] > 0) inc.push(arrowText(j, k, Bold[j][k]));
      if (Bold[k][j] > 0) inc.push(arrowText(k, j, Bold[k][j]));
    }
    const st = stages[3];
    const cancel = [], frozenCut = [];
    for (let i = 0; i < n; i++) {
      for (let j = i + 1; j < n; j++) {
        const m = st.hl[i][j] + st.hl[j][i];
        if (!m) continue;
        if (fr[i] && fr[j]) frozenCut.push('$' + T(i) + '\\text{–}' + T(j) + '$');
        else cancel.push('$' + T(i) + '\\rightleftarrows ' + T(j) + (st.hl[i][j] > 1 ? '\\ (\\times ' + st.hl[i][j] + ')' : '') + '$');
      }
    }
    const rows = [];
    for (let i = 0; i < n; i++) {
      for (let j = i + 1; j < n; j++) {
        if (i === k || j === k || Bnew[i][j] === Bold[i][j]) continue;
        const bik = Bold[i][k], bkj = Bold[k][j];
        if (fr[i] && fr[j]) { rows.push("b'_{" + sub2(T(i), T(j)) + '} &= 0 \\quad\\text{(both frozen)}'); continue; }
        rows.push("b'_{" + sub2(T(i), T(j)) + '} &= ' + Bold[i][j] + ' + \\tfrac12\\bigl(|' + bik + '|\\cdot ' + par(bkj) + ' + ' + par(bik) + '\\cdot|' + bkj + '|\\bigr) = ' + Bnew[i][j]);
      }
    }
    const shown = rows.slice(0, 6);
    return [
      '**Step 1** (compose). ' + (paths.length ? 'For each path $i\\to ' + K + '\\to j$ add an arrow $i\\to j$: ' + listT(paths) + '.' : 'There is no path $i\\to ' + K + '\\to j$, so no arrow is added.'),
      '**Step 2** (reverse). ' + (inc.length ? 'Reverse the arrows incident to $' + K + '$: ' + listT(inc) + '.' : 'There are no arrows at $' + K + '$.'),
      '**Step 3** (cancel). ' + (cancel.length ? 'Remove the 2-cycles ' + listT(cancel) : 'There are no 2-cycles') +
        (frozenCut.length ? ', and the arrows between frozen vertices ' + listT(frozenCut) : '') + '.',
      '**Matrix check.** By the Fomin–Zelevinsky formula $$\\begin{aligned} b\'_{' + sub2('i', K) + '} &= -b_{' + sub2('i', K) + '},\\\\ b\'_{ij} &= b_{ij} + \\tfrac12\\bigl(|b_{' + sub2('i', K) + '}|\\,b_{' + sub2(K, 'j') + '} + b_{' + sub2('i', K) + '}\\,|b_{' + sub2(K, 'j') + '}|\\bigr) \\quad (i,j\\neq ' + K + ').\\end{aligned}$$',
      shown.length ? 'The entries that change are $$\\begin{aligned}' + shown.join('\\\\ ') + '\\end{aligned}$$' + (rows.length > 6 ? ' and ' + (rows.length - 6) + ' more.' : '') : 'Apart from row and column $' + K + '$, no entry changes.',
      'Both descriptions give the same skew-symmetric matrix, which is the quiver shown.'
    ];
  }

  /** 示例 / 导入的箭头列表 */
  function arrowList() {
    const arr = [];
    state.B.forEach((row, i) => row.forEach((x, j) => { if (x > 0) arr.push(arrowText(i, j, x)); }));
    return arr;
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
    proof('Undo', ['Restored the previous state; $B$ is again the matrix from before the last step.']);
  }
  function redo() {
    if (!redoStack.length) return;
    stopDemo();
    undoStack.push(snapshot());
    restore(redoStack.pop());
    render();
    proof('Redo', ['Re-applied the step that was undone.']);
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
    const n = state.vertices.length;
    proof('Add a ' + (v.frozen ? 'frozen' : 'mutable') + ' vertex $' + texEsc(v.label) + '$', [
      'The exchange matrix gains a zero row and a zero column, so now $B \\in M_{' + n + '}(\\mathbb{Z})$.',
      v.frozen ? 'The vertex is frozen: it is never mutated, and an ice quiver has no arrows between frozen vertices.' : 'The vertex is mutable, so $\\mu_{' + texEsc(v.label) + '}$ may be applied.'
    ]);
  }

  function removeVertexAt(i) {
    state.vertices.splice(i, 1);
    state.B.splice(i, 1);
    state.B.forEach((row) => row.splice(i, 1));
  }

  function deleteVertex(id) {
    const i = idx(id);
    if (i < 0) return;
    const label = state.vertices[i].label;
    const gone = [];
    state.B[i].forEach((x, j) => { if (x > 0) gone.push(arrowText(i, j, x)); if (x < 0) gone.push(arrowText(j, i, -x)); });
    pushUndo();
    structural();
    removeVertexAt(i);
    if (selected === id) selected = null;
    render();
    proof('Delete vertex $' + texEsc(label) + '$', [
      'Delete row and column $' + texEsc(label) + '$ of $B$' + (gone.length ? ', together with the arrows ' + listT(gone) : '') + '.',
      'What remains is a principal submatrix of $B$, hence still skew-symmetric.'
    ]);
  }

  function addArrow(fromId, toId) {
    const i = idx(fromId), j = idx(toId);
    if (i < 0 || j < 0) return;
    if (i === j) { toast('Loops (1-cycles) are not allowed in a quiver.'); return; }
    const vi = state.vertices[i], vj = state.vertices[j];
    if (vi.frozen && vj.frozen) { toast('Ice quivers have no arrows between frozen vertices.'); return; }
    pushUndo();
    structural();
    const before = state.B[i][j];
    state.B[i][j] += 1;
    state.B[j][i] -= 1;
    if (state.B[i][j] <= 0) toast('Cancelled against an arrow in the opposite direction (quivers have no 2-cycles).');
    render();
    const now = state.B[i][j];
    proof('Draw an arrow $' + T(i) + '\\to ' + T(j) + '$', [
      '$' + bij(i, j) + ' = ' + before + ' + 1 = ' + now + '$, and by skew-symmetry $' + bij(j, i) + ' = -' + bij(i, j) + ' = ' + (-now || 0) + '$.',
      now > 0 ? 'Hence there ' + (now === 1 ? 'is one arrow' : 'are $' + now + '$ arrows') + ' $' + T(i) + '\\to ' + T(j) + '$.'
        : 'The new arrow cancels an arrow $' + T(j) + '\\to ' + T(i) + '$, since a quiver has no 2-cycles; ' + (now === 0 ? 'no arrows remain between them.' : '$' + (-now) + '$ arrow(s) $' + T(j) + '\\to ' + T(i) + '$ remain.')
    ]);
  }

  function removeArrow(i, j) {
    if (!(state.B[i] && state.B[i][j] > 0)) return;
    pushUndo();
    structural();
    state.B[i][j] -= 1;
    state.B[j][i] += 1;
    render();
    proof('Delete an arrow $' + T(i) + '\\to ' + T(j) + '$', [
      '$' + bij(i, j) + ' = ' + (state.B[i][j] + 1) + ' - 1 = ' + state.B[i][j] + '$ and $' + bij(j, i) + ' = ' + state.B[j][i] + '$.'
    ]);
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
      if (removed) toast('Removed ' + removed + ' arrow(s) between frozen vertices.');
      render();
      proof('Freeze vertex $' + T(i) + '$', [
        'A frozen vertex is never mutated: its row stays in $\\tilde B$, but its column is dropped.',
        removed ? 'An ice quiver has no arrows between frozen vertices, so $' + removed + '$ arrow(s) were removed.' : 'It had no arrows to other frozen vertices, so $B$ is unchanged.'
      ]);
      return;
    }
    render();
    proof('Unfreeze vertex $' + T(i) + '$', ['The vertex becomes mutable: its column is added to $\\tilde B$ and $\\mu_{' + T(i) + '}$ is allowed.']);
  }

  function setEntry(i, j, v) {
    if (i === j) return;
    const fr = frozenArr();
    if (fr[i] && fr[j]) return;
    if (state.B[i][j] === v) return;
    pushUndo();
    structural();
    const old = state.B[i][j];
    state.B[i][j] = v;
    state.B[j][i] = -v || 0;
    render();
    proof('Edit the entry $' + bij(i, j) + '$', [
      '$' + bij(i, j) + '$ changes from $' + old + '$ to $' + v + '$, and by skew-symmetry $' + bij(j, i) + ' = ' + (-v || 0) + '$.',
      v > 0 ? 'Hence there are $' + v + '$ arrow(s) $' + T(i) + '\\to ' + T(j) + '$.' : v < 0 ? 'Hence there are $' + (-v) + '$ arrow(s) $' + T(j) + '\\to ' + T(i) + '$.' : 'Hence there are no arrows between them.'
    ]);
  }

  function setLabel(id, label) {
    const v = byId(id);
    label = label.trim();
    if (!v || label === v.label) return;
    if (!label) { toast('The label cannot be empty.'); render(); return; }
    if (/[\s,，;]/.test(label)) { toast('Labels cannot contain spaces or commas.'); render(); return; }
    if (state.vertices.some((w) => w !== v && w.label === label)) { toast('The label “' + label + '” is already in use.'); render(); return; }
    const old = v.label;
    pushUndo();
    v.label = label;
    render();
    proof('Rename vertex $' + texEsc(old) + '$ to $' + texEsc(label) + '$', ['Only the name changes; $B$ is unchanged.']);
  }

  // ---------------------------------------------------------------- 变异
  function applyMutation(i) {
    const fr = frozenArr();
    if (!state.seq.length) state.seed = JSON.stringify(state.B);
    const stages = Q.mutationStages(state.B, i, fr);
    const Bold = state.B;
    state.B = Q.mutate(state.B, i, fr);
    state.seq.push(state.vertices[i].id);
    proof('Mutation $\\mu_{' + T(i) + '}$', mutationProof(Bold, state.B, i, fr, stages), { proof: true, qed: true });
    return stages;
  }

  function mutateAt(id) {
    const i = idx(id);
    if (i < 0) return;
    if (state.vertices[i].frozen) { toast('Cannot mutate at a frozen vertex.'); return; }
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
    if (!tokens.length) { toast('Enter a mutation sequence, e.g. 1 2 1'); return; }
    const ids = [];
    for (const t of tokens) {
      const v = state.vertices.find((w) => w.label === t);
      if (!v) { toast('No vertex has the label “' + t + '”.'); return; }
      if (v.frozen) { toast('“' + t + '” is a frozen vertex and cannot be mutated.'); return; }
      ids.push(v.id);
    }
    if (ids.length === 1) { mutateAt(ids[0]); return; }
    stopDemo();
    pushUndo();
    ids.forEach((id) => applyMutation(idx(id)));
    render();
    flash(ids[ids.length - 1]);
    toast('Applied ' + ids.length + ' mutations.');
  }

  function randomMutation() {
    const last = state.seq[state.seq.length - 1];
    let cand = state.vertices.filter((v) => !v.frozen && v.id !== last);
    if (!cand.length) cand = state.vertices.filter((v) => !v.frozen);
    if (!cand.length) { toast('There are no mutable vertices.'); return; }
    mutateAt(cand[Math.floor(Math.random() * cand.length)].id);
  }

  function backToSeed() {
    if (!state.seed) { toast('No mutations have been applied yet.'); return; }
    stopDemo();
    pushUndo();
    const seqLabels = state.seq.map((id) => { const v = byId(id); return '\\mu_{' + (v ? texEsc(v.label) : '?') + '}'; });
    state.B = JSON.parse(state.seed);
    state.seq = [];
    state.seed = null;
    render();
    toast('Back to the initial seed.');
    proof('Back to the initial seed', [
      'Restored $B$ from before $' + seqLabels.slice().reverse().join('\\circ ') + '$.',
      'Since each $\\mu_k$ is an involution, this is the same as applying $' + seqLabels.join('\\circ ') + '$ to the current seed.'
    ], { proof: false });
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
    if (!mutable.length) { toast('There are no mutable vertices.'); return; }
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
    toast(sign > 0 ? 'Added principal coefficients: i → i′.' : 'Added coprincipal coefficients: i′ → i.');
    proof(sign > 0 ? 'Add principal coefficients' : 'Add coprincipal coefficients', [
      'For each of the $' + mutable.length + '$ mutable vertices $i$, add a frozen vertex $i\'$ and an arrow $' + (sign > 0 ? "i\\to i'" : "i'\\to i") + '$.',
      'Thus the coefficient block of $\\tilde B$ (rows $i\'$, columns $i$) is $' + (sign > 0 ? '-I' : 'I') + '$' + (sign > 0 ? '; after mutations its columns are, up to sign, the $c$-vectors.' : '.')
    ]);
  }

  function unfreezeAll() {
    if (!state.vertices.some((v) => v.frozen)) { toast('There are no frozen vertices.'); return; }
    pushUndo();
    structural();
    const cnt = state.vertices.filter((v) => v.frozen).length;
    state.vertices.forEach((v) => { v.frozen = false; });
    render();
    proof('Unfreeze all', ['$' + cnt + '$ frozen vertices become mutable; $B$ is unchanged and $\\tilde B$ is now the full matrix.']);
  }

  function removeFrozen() {
    if (!state.vertices.some((v) => v.frozen)) { toast('There are no frozen vertices.'); return; }
    pushUndo();
    structural();
    proof('Remove frozen vertices', ['Delete the rows and columns of ' + listT(state.vertices.filter((v) => v.frozen).map((v) => '$' + texEsc(v.label) + '$')) + '; what remains is the principal part $B$ of $\\tilde B$.']);
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
    proof('Clear', ['The quiver is empty, and $B$ is the $0\\times 0$ matrix.']);
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
    D4tilde: {
      verts: [['1', -1.8, -1.4], ['2', 1.8, -1.4], ['3', -1.8, 1.4], ['4', 1.8, 1.4], ['5', 0, 0]],
      arrows: [['1', '5', 1], ['2', '5', 1], ['3', '5', 1], ['4', '5', 1]]
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
    const opt = document.querySelector('#preset option[value="' + name + '"]');
    const arr = arrowList();
    const fz = state.vertices.filter((v) => v.frozen).map((v) => v.label);
    proof('Load example ' + (opt ? opt.textContent : name), [
      '$' + state.vertices.length + '$ vertices' + (fz.length ? ' (frozen: ' + listT(fz.map((l) => '$' + texEsc(l) + '$')) + ')' : '') + '; arrows: ' + (arr.length ? listT(arr, 10) : 'none') + '.',
      '$B$ is the skew-symmetric matrix with $b_{ij} = \\#\\{i\\to j\\} - \\#\\{j\\to i\\}$.'
    ]);
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

  /** 维数向量的证明：按路的长度逐层计数 */
  function moduleProof(kind, id) {
    const info = computePA();
    const a = info.verts.indexOf(idx(id));
    if (a < 0) return;
    const L = texEsc(byId(id).label);
    const name = kind + '(' + L + ')';
    const dims = moduleDims(info, kind, a);
    const vec = '(' + dims.map((x) => (x === null ? '\\infty' : x.toString())).join(',') + ')';
    const title = 'Dimension vector of $' + name + '$';
    if (kind === 'S') {
      proof(title, ['$S(' + L + ')$ is $k$ at $' + L + '$ and $0$ elsewhere, and every arrow acts by $0$; hence $\\underline{\\dim}\\,S(' + L + ') = ' + vec + '$.'], { proof: true, qed: true });
      return;
    }
    const isP = kind === 'P';
    const lines = [isP
      ? '$P(' + L + ')_j$ has a basis consisting of the paths from $' + L + '$ to $j$, so $$\\underline{\\dim}\\,P(' + L + ')_j = \\sum_{\\ell\\ge 0}(A^\\ell)_{' + sub2(L, 'j') + '}.$$'
      : '$I(' + L + ')_j$ has a basis consisting of the paths from $j$ to $' + L + '$, so $$\\underline{\\dim}\\,I(' + L + ')_j = \\sum_{\\ell\\ge 0}(A^\\ell)_{' + sub2('j', L) + '}.$$'];
    const ls = Q.layers(info.pa, a, kind).filter((v) => v.some((x) => x > 0n));
    const layerTex = (v) => {
      const parts = [];
      v.forEach((m, j) => { if (m > 0n) parts.push('S_{' + texEsc(state.vertices[info.verts[j]].label) + '}' + (m > 1n ? '^{' + m + '}' : '')); });
      return parts.join('\\oplus ');
    };
    const rows = ls.slice(0, 8).map((v, l) => '\\ell = ' + l + '&:\\ ' + layerTex(v));
    lines.push((isP ? 'Grouping the paths by length $\\ell$ (these are the radical layers):' : 'Grouping the paths by length $\\ell$ (these are the socle layers):') +
      ' $$\\begin{aligned}' + rows.join('\\\\ ') + '\\end{aligned}$$' + (ls.length > 8 ? ' and further layers.' : ''));
    if (dims.some((x) => x === null)) lines.push('Some of these paths run through an oriented cycle, so there are infinitely many of them and the corresponding entries are $\\infty$.');
    else if (info.opts.trunc) lines.push('In $kQ/R^{' + info.opts.L + '}$ all paths of length $\\ge ' + info.opts.L + '$ vanish.');
    lines.push('Adding up the layers, $\\underline{\\dim}\\,' + name + ' = ' + vec + '$, of total dimension $' + (Q.totalDim(dims) === null ? '\\infty' : Q.totalDim(dims).toString()) + '$.');
    proof(title, lines, { proof: true, qed: true });
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
      html = '<span class="hint">No vertices.</span>';
    } else {
      html += '<div>dim ' + algName + ' = <span class="big">' + fmt(pa.dim) + '</span></div>';
      if (!pa.acyclic) {
        const cyc = pa.onCycle.map((a) => V[info.verts[a]].label).join(', ');
        html += '<div class="' + (o.trunc ? 'hint' : 'warn') + '">Q has an oriented cycle (through ' + cyc + ')' +
          (o.trunc ? '.' : ', so kQ is infinite-dimensional; try “Truncated”.') + '</div>';
      }
      html += '<dl>' +
        '<dt>Vertices / arrows</dt><dd>' + info.verts.length + ' / ' + nArrows + '</dd>' +
        '<dt>Oriented cycles</dt><dd>' + (pa.acyclic ? 'none (Q is acyclic)' : 'yes') + '</dd>' +
        '<dt>Loewy length</dt><dd>' + (pa.loewy != null ? pa.loewy : '∞') + '</dd>' +
        (pa.finite && pa.loewy ? '<dt>Longest nonzero path</dt><dd>' + (pa.loewy - 1) + '</dd>' : '') +
        '</dl>';
    }
    $('pa-summary').innerHTML = html;

    // 维数向量表
    const kind = $('pa-kind').value;
    const esc = (t) => t.replace(/[&<>"]/g, (ch) => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' }[ch]));
    if (modHL && (idx(modHL.id) < 0 || info.verts.indexOf(idx(modHL.id)) < 0)) modHL = null;
    let t = '';
    if (info.verts.length) {
      t += '<thead><tr><th>Module</th>' + info.verts.map((i) => '<th class="' + (V[i].frozen ? 'frozen' : '') + '">' + esc(V[i].label) + '</th>').join('') + '<th>dim</th></tr></thead><tbody>';
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
      title.textContent = modName(modHL.kind, label) + (isP ? ': radical layers (top down)' : ': socle layers (bottom up)');
      box.appendChild(title);
      const lw = document.createElement('div');
      lw.className = 'loewy';
      const rows = ls.map((vec, l) => ({ name: (isP ? (l === 0 ? 'top' : 'rad' + sup(l)) : (l === 0 ? 'socle' : 'soc' + sup(l + 1))), text: layerText(vec, info) }));
      if (!pa.finite) rows.push({ name: '…', text: '(infinitely many layers)' });
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
        ? 'Layer l = endpoints of the paths of length l starting at ' + label + '.'
        : 'Layer l from the bottom = starting points of the paths of length l ending at ' + label + '.';
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

  function texNodeName(nd, info) {
    const l = texEsc(vlabel(info, nd.i));
    if (nd.kind === 'P') return nd.r === 0 ? 'P_{' + l + '}' : '\\tau^{-' + nd.r + '}P_{' + l + '}';
    return nd.r === 0 ? 'I_{' + l + '}' : '\\tau' + (nd.r === 1 ? '' : '^{' + nd.r + '}') + 'I_{' + l + '}';
  }

  function dimLabel(dim) {
    return dim.length <= 12 && dim.every((x) => x < 10) ? dim.join('') : dim.join(',');
  }

  function arSummary(value) {
    const ar = value.ar, info = value.info;
    if (!ar.ok) {
      if (ar.reason === 'empty') return 'No vertices.';
      const esc = (t) => t.replace(/[&<>"]/g, (ch) => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' }[ch]));
      const cyc = (ar.cycle || []).map((a) => vlabel(info, a));
      const cycText = cyc.length ? ' (e.g. ' + esc(cyc.concat(cyc[0]).join(' → ')) + ')' : '';
      return '<span class="ar-warn">The quiver has an oriented cycle' + cycText + ', so kQ is infinite-dimensional and the AR quiver cannot be computed.</span>' +
        'Only path algebras of acyclic quivers are supported.';
    }
    const kindName = { dynkin: '', euclidean: ' Euclidean', wild: '' };
    const names = ar.comps.map((c) => c.name + kindName[c.kind]).join(' ⊔ ');
    let html;
    if (ar.finite) {
      html = 'Representation-finite (' + names + '): <b>' + ar.total + '</b> indecomposable modules (in bijection with the positive roots).';
    } else {
      html = 'Representation-infinite (' + names + '). Showing the first ' + ar.layers + ' layers of the preprojective and preinjective components';
      const tubeText = ar.comps.filter((c) => c.kind === 'euclidean' && c.regular && c.regular.ok).map((c) => {
        const rk = c.regular.tubes.map((t) => t.rank);
        return (rk.length ? 'exceptional tubes of rank ' + rk.join(', ') + ' and ' : '') + 'homogeneous tubes';
      });
      if (tubeText.length) html += '; the regular components form a ℙ¹-family of tubes (' + tubeText.join('; ') + ')';
      if (ar.comps.some((c) => c.kind === 'wild')) html += '; the regular components of wild type (infinitely many components of type ℤA∞) are not drawn';
      html += '.';
    }
    if (info.opts.trunc) html += ' Note: computed for kQ without relations, ignoring the truncation.';
    return html;
  }

  function renderARSummary() {
    const value = computeAR();
    $('ar-summary').innerHTML = arSummary(value);
    $('btn-ar').disabled = false;
    $('btn-ar').textContent = value.ar.ok ? 'Show AR quiver' : 'Show AR quiver (not available now)';
  }

  /** 箭图有圈时，给出可以得到无圈箭图的操作 */
  function arFixes(value) {
    const box = $('ar-info');
    box.innerHTML = '';
    if (value.ar.reason !== 'cyclic') return;
    box.append('You can try: ');
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
      if (mut.length && AR.topoOrder(A)) add('Mutable part only (it is acyclic)', () => { $('pa-mutable').checked = true; render(); });
    }
    if (state.seed) add('Back to initial seed', backToSeed);
    if (undoStack.length) add('Undo last step', undo);
    add('Open example A₃', () => loadPreset('A3'));
    const p = document.createElement('p');
    p.className = 'hint';
    p.textContent = 'Mutation often creates oriented cycles; the AR quiver can only be computed when the quiver is acyclic (for example, an orientation of a Dynkin diagram).';
    box.append(p);
  }

  function openAR() {
    arSel = null;
    arScale = null;
    $('dlg-ar').showModal();
    drawAR();
  }

  // ---- 导出范畴 / 丛范畴
  let derCache = { key: null, value: null };
  function arShiftRange() {
    let a = parseInt($('ar-dmin').value, 10), b = parseInt($('ar-dmax').value, 10);
    if (!Number.isFinite(a)) a = 0;
    if (!Number.isFinite(b)) b = 1;
    a = Math.max(-5, Math.min(5, a));
    b = Math.max(-5, Math.min(5, b));
    if (b < a) { const t = a; a = b; b = t; }
    return [a, Math.min(b, a + 5)];
  }
  function computeDerived(cat) {
    const info = computePA();
    const [a, b] = arShiftRange();
    const layers = arLayers();
    const key = JSON.stringify([state.B, info.verts, cat, a, b, layers]);
    if (derCache.key === key) return derCache.value;
    const A = info.verts.map((i) => info.verts.map((j) => Math.max(state.B[i][j], 0)));
    const D = AR.derivedQuiver(A, { category: cat, dmin: a, dmax: b, layers: layers });
    derCache = { key: key, value: D };
    return D;
  }
  function derivedSummary(D, value) {
    const info = value.info;
    const n = info.verts.length;
    const names = D.comps.map((c) => c.name + (c.kind === 'euclidean' ? ' Euclidean' : '')).join(' ⊔ ');
    const dyn = D.comps.every((c) => c.kind === 'dynkin');
    const euclid = D.comps.some((c) => c.kind === 'euclidean');
    const wild = D.comps.some((c) => c.kind === 'wild');
    const shown = D.nodes.filter((x) => !x.ghost).length;
    if (D.category === 'derived') {
      if (dyn) {
        return '<b>D<sup>b</sup>(mod kQ)</b> (' + names + '): the AR quiver is ℤQ (Happel’s theorem). Each shift [d] is a copy of mod kQ, and consecutive copies are joined by τ⁻¹I(j) = P(j)[1]. ' +
          'Showing shifts [' + D.dmin + '] to [' + D.dmax + '], ' + shown + ' objects in total; objects with an odd shift are shaded.';
      }
      return '<b>D<sup>b</sup>(mod kQ)</b> (' + names + '): showing the component containing the projectives, ℤQ = preinjectives[−1] ∪ preprojectives, ' + D.layers + ' τ-steps in each direction. ' +
        'The other components are its shifts [d] and the shifts of the regular components' + (euclid ? ' (tubes for Euclidean type; the tubes in degree [0] are drawn below)' : '') + (wild ? ' (of type ℤA∞ for wild type, not drawn)' : '') + '.';
    }
    if (dyn) {
      return '<b>Cluster category C<sub>Q</sub> = D<sup>b</sup>/τ⁻¹[1]</b> (' + names + '): <b>' + D.total + '</b> indecomposable objects = ' + (D.total - n) + ' indecomposable modules + ' + n +
        ' objects P(i)[1] (red), in bijection with the cluster variables of the cluster algebra. Dashed boxes repeat P(i) to show the wrap-around τ⁻¹(P(i)[1]) = P(i).';
    }
    return '<b>Cluster category C<sub>Q</sub> = D<sup>b</sup>/τ⁻¹[1]</b> (' + names + '): the transjective component is ℤQ: … → τI → I → P[1] → P → τ⁻¹P → … (about ' + D.layers + ' steps in each direction; P(i)[1] in red); ' +
      'the regular components are the same as in mod kQ' + (euclid ? ' (tubes drawn below)' : '') + (wild ? ' (not drawn for wild type)' : '') + '.';
  }

  function drawAR() {
    const value = computeAR();
    const ar = value.ar, info = value.info;
    const eE = $('ar-edges'), eN = $('ar-nodes'), svgAR = $('ar-canvas');
    eE.textContent = '';
    eN.textContent = '';
    $('ar-desc').innerHTML = arSummary(value);
    $('ar-layers-wrap').hidden = !ar.ok || ar.finite;
    const hasEuclid = ar.ok && ar.comps.some((c) => c.kind === 'euclidean');
    $('ar-reg-wrap').hidden = !hasEuclid;
    $('ar-order').textContent = ar.ok ? 'Vertex order in dimension vectors: (' + info.verts.map((i) => state.vertices[i].label).join(', ') + ')' : '';
    document.querySelectorAll('.ar-controls, .ar-stage, .ar-legend').forEach((x) => { x.hidden = !ar.ok; });
    $('dlg-ar').classList.toggle('compact', !ar.ok);
    if (!ar.ok) {
      svgAR.setAttribute('width', 0);
      svgAR.setAttribute('height', 0);
      arFixes(value);
      arDrawn = null;
      return;
    }

    // ---- 选择范畴
    const cat = $('ar-cat').value;
    const D = cat === 'mod' ? null : computeDerived(cat);
    const src = D || ar;
    const hasInf = src.comps.some((c) => c.kind !== 'dynkin');
    if (D) $('ar-desc').innerHTML = derivedSummary(D, value);
    $('ar-layers-wrap').hidden = !hasInf;
    $('ar-shift-wrap').hidden = !(cat === 'derived' && src.comps.some((c) => c.kind === 'dynkin'));

    // ---- 统一的绘制对象：AR 箭图中的对象 + 管中的模
    const mode = $('ar-label').value;
    const showReg = hasEuclid && $('ar-reg').checked;
    const L = arLayers();
    const modNames = new Map();
    const modTex = new Map();
    ar.nodes.forEach((nd) => {
      const k = nd.dim.join(',');
      if (!modNames.has(k)) { modNames.set(k, arNodeName(nd, info)); modTex.set(k, texNodeName(nd, info)); }
    });
    const derItem = (nd) => {
      let name, dimText, tex;
      if (nd.shiftP >= 0) {
        name = dimText = 'P' + vlabel(info, nd.shiftP) + '[1]';
        tex = 'P_{' + texEsc(vlabel(info, nd.shiftP)) + '}[1]';
      } else {
        const suf = nd.deg ? '[' + nd.deg + ']' : '';
        name = (modNames.get(nd.dim.join(',')) || '(' + nd.dim.join(',') + ')') + suf;
        tex = (modTex.get(nd.dim.join(',')) || texVec(nd.dim)) + suf;
        dimText = dimLabel(nd.dim) + suf;
      }
      const plain = nd.deg === 0 && nd.shiftP < 0;
      return {
        id: nd.id, kind: 'der', nd: nd, dim: nd.dim, name: name, dimText: dimText, tex: tex,
        proj: plain && nd.proj >= 0, inj: plain && nd.inj >= 0, simple: plain && nd.simple,
        ghost: nd.ghost, odd: nd.deg % 2 !== 0, shiftp: nd.shiftP >= 0
      };
    };
    const items = D ? D.nodes.map(derItem) : ar.nodes.map((nd) => ({
      id: nd.id, kind: 'ar', nd: nd, dim: nd.dim,
      name: arNodeName(nd, info), tex: texNodeName(nd, info),
      proj: nd.proj >= 0, inj: nd.inj >= 0, simple: nd.simple
    }));
    const links = src.edges.map((e) => ({ from: e.from, to: e.to, mult: e.mult, curve: Math.abs(src.nodes[e.from].row - src.nodes[e.to].row) >= 2 }));
    const taus = src.tau.slice();
    const tubeBoxes = []; // 管的外框信息
    if (showReg) {
      src.comps.forEach((c, ci) => {
        if (c.kind !== 'euclidean' || !c.regular) return;
        if (!c.regular.ok) { tubeBoxes.push({ comp: c, failed: true }); return; }
        const list = c.regular.tubes.map((t, ti) => ({ rank: t.rank, simples: t.simples, homog: false, index: ti + 1 }));
        list.push({ rank: 1, simples: [c.regular.delta], homog: true, index: 0 });
        list.forEach((tube) => {
          const r = tube.rank;
          const at = new Map();
          const box = { comp: c, tube: tube, cells: [] };
          for (let l = 1; l <= L; l++) {
            for (let x = (l - 1) % 2; x <= 2 * r; x += 2) {
              const k = ((-(x - (l - 1)) / 2) % r + r) % r;
              const dim = AR.tubeModuleDim(tube, k, l);
              const it = {
                id: items.length, kind: 'tube', dim: dim, tube: tube, k: k, l: l, tx: x, ghost: x === 2 * r, comp: ci,
                name: tube.homog ? 'Mλ[' + l + ']' : 'E' + (k + 1) + '[' + l + ']',
                tex: tube.homog ? 'M_\\lambda[' + l + ']' : 'E_{' + (k + 1) + '}[' + l + ']',
                proj: false, inj: false, simple: dim.reduce((a, b) => a + b, 0) === 1
              };
              items.push(it);
              box.cells.push(it);
              at.set(x + ':' + l, it.id);
            }
          }
          box.cells.forEach((it) => {
            [[1, 1], [1, -1]].forEach(([dx, dl]) => {
              const to = at.get((it.tx + dx) + ':' + (it.l + dl));
              if (to != null) links.push({ from: it.id, to: to, mult: 1, curve: false });
            });
            const left = at.get((it.tx - 2) + ':' + it.l);
            if (left != null) taus.push({ from: it.id, to: left });
          });
          tubeBoxes.push(box);
        });
      });
    }
    if (arSel != null && !items[arSel]) arSel = null;

    const text = (it) => (mode === 'name' ? it.name : (it.dimText || dimLabel(it.dim)));
    const widths = items.map((it) => Math.max(26, text(it).length * 7.4 + 12));
    const maxW = Math.max.apply(null, widths);
    const UX = Math.max(26, (maxW + 12) / 2), UY = 46, PAD = 34, HH = 11;
    const multi = src.comps.length > 1;
    const nodes = src.nodes;
    const minX = Math.min.apply(null, nodes.map((nd) => nd.x));
    const maxX = Math.max.apply(null, nodes.map((nd) => nd.x));
    const maxRow = Math.max.apply(null, nodes.map((nd) => nd.row));
    const left = PAD + maxW / 2 + (multi ? 40 : 0);
    let W = left + (maxX - minX) * UX + PAD + maxW / 2;
    let H = PAD * 2 + maxRow * UY;
    nodes.forEach((nd) => { items[nd.id].X = left + (nd.x - minX) * UX; items[nd.id].Y = PAD + nd.row * UY; });

    // 管的布局：放在主图下方，从左到右排列，拟长度 1（管口）在最下面
    const decorations = [];
    if (tubeBoxes.length) {
      const top = PAD + (maxRow + 1.4) * UY;
      decorations.push({ type: 'band', y: top - 0.55 * UY });
      let cursor = left;
      tubeBoxes.forEach((b) => {
        if (b.failed) {
          decorations.push({ type: 'text', x: cursor, y: top + UY, text: b.comp.name + ': δ is too large; tubes not computed.', anchor: 'start' });
          cursor += 12 * UX;
          return;
        }
        const r = b.tube.rank;
        const x0 = cursor;
        b.cells.forEach((it) => { it.X = x0 + it.tx * UX; it.Y = top + 1.15 * UY + (L - it.l) * UY; });
        const bottom = top + 1.15 * UY + (L - 1) * UY;
        const title = (multi ? b.comp.name + ' · ' : '') + (b.tube.homog ? 'Homogeneous tube (rank 1)' : 'Exceptional tube ' + b.tube.index + ' (rank ' + r + ')') + (cat === 'derived' ? ' [0]' : '');
        decorations.push({ type: 'text', x: x0 + r * UX, y: top, text: title, cls: 'ar-tube-title' });
        decorations.push({ type: 'vline', x: x0, y1: top + 0.45 * UY, y2: bottom + 0.5 * UY });
        decorations.push({ type: 'vline', x: x0 + 2 * r * UX, y1: top + 0.45 * UY, y2: bottom + 0.5 * UY });
        decorations.push({ type: 'text', x: x0 + r * UX, y: bottom + 0.85 * UY, text: b.tube.homog ? 'one for each remaining point of ℙ¹' : 'the two dashed edges are glued', cls: 'ar-tube-note' });
        cursor = x0 + 2 * r * UX + Math.max(4 * UX, maxW + 24);
        W = Math.max(W, x0 + 2 * r * UX + PAD + maxW / 2);
        H = Math.max(H, bottom + 0.85 * UY + PAD);
      });
    }

    // 邻居
    const nb = new Set();
    if (arSel != null) {
      links.forEach((e) => {
        if (e.from === arSel) nb.add(e.to);
        if (e.to === arSel) nb.add(e.from);
      });
    }

    const trim = (w, dx, dy) => Math.min(Math.abs(dx) > 1e-9 ? w / Math.abs(dx) : Infinity, Math.abs(dy) > 1e-9 ? (HH + 3) / Math.abs(dy) : Infinity);

    // 装饰：分隔线、管的边界与标题
    decorations.forEach((d) => {
      if (d.type === 'band') el('line', { x1: PAD / 2, y1: d.y, x2: W - PAD / 2, y2: d.y, class: 'ar-band' }, eE);
      else if (d.type === 'vline') el('line', { x1: d.x, y1: d.y1, x2: d.x, y2: d.y2, class: 'ar-glue' }, eE);
      else el('text', { x: d.x, y: d.y, class: d.cls || 'ar-gap', 'text-anchor': d.anchor || 'middle' }, eN).textContent = d.text;
    });

    // τ（虚线）
    if ($('ar-tau').checked) {
      taus.forEach((t) => {
        const a = items[t.from], b = items[t.to];
        el('line', { x1: a.X - widths[a.id] / 2 - 3, y1: a.Y, x2: b.X + widths[b.id] / 2 + 3, y2: b.Y, class: 'ar-tau' }, eE);
      });
    }

    // 不可约映射
    links.forEach((e) => {
      const a = items[e.from], b = items[e.to];
      const p = { X: a.X, Y: a.Y }, q = { X: b.X, Y: b.Y };
      const hl = arSel != null && (e.from === arSel || e.to === arSel);
      const dx = q.X - p.X, dy = q.Y - p.Y, len = Math.hypot(dx, dy);
      const nx = -dy / len, ny = dx / len;
      const bend = e.curve ? 0.22 * len : 0;
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
    src.comps.forEach((c) => {
      const yMid = PAD + (c.rowStart + (c.rows - 1) / 2) * UY;
      if (multi) el('text', { x: 8, y: yMid, class: 'ar-comp', 'dominant-baseline': 'central' }, eN).textContent = c.name;
      if (c.gapX != null) {
        const label = c.kind === 'wild' ? '⋯ wild ⋯' : (showReg ? '⋯ tubes ↓ ⋯' : '⋯ regular ⋯');
        el('text', { x: left + (c.gapX - minX) * UX, y: yMid, class: 'ar-gap' }, eN).textContent = label;
      }
    });
    // 管顶的省略号
    tubeBoxes.forEach((b) => {
      if (b.failed) return;
      const topRow = b.cells.filter((it) => it.l === L);
      if (topRow.length) el('text', { x: b.cells[0].X + b.tube.rank * UX, y: topRow[0].Y - 0.58 * UY, class: 'ar-gap' }, eN).textContent = '⋮';
    });

    // 模
    items.forEach((it) => {
      let cls = 'ar-node';
      if (it.proj) cls += ' proj';
      if (it.inj) cls += ' inj';
      if (it.simple) cls += ' simple';
      if (it.kind === 'tube') cls += ' regular' + (it.l === 1 ? ' rsimple' : '');
      if (it.ghost) cls += ' ghost';
      if (it.odd) cls += ' odd';
      if (it.shiftp) cls += ' shiftp';
      if (it.id === arSel) cls += ' sel';
      else if (nb.has(it.id)) cls += ' nb';
      const g = el('g', { class: cls, transform: 'translate(' + it.X + ',' + it.Y + ')', 'data-ar': it.id }, eN);
      el('title', {}, g).textContent = it.name + '  dim = (' + it.dim.join(', ') + ')';
      el('rect', { x: -widths[it.id] / 2, y: -HH, width: widths[it.id], height: 2 * HH, rx: 5 }, g);
      el('text', {}, g).textContent = text(it);
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

    arDrawn = { items: items, links: links, value: value, src: src, cat: cat };
    renderARInfo();
    renderARProof();
  }

  let arDrawn = null;

  // ---- AR 箭图的证明（LaTeX）
  const KIND_REASON = {
    dynkin: 'a Dynkin diagram; hence $kQ$ is representation-finite by Gabriel’s theorem',
    euclidean: 'a Euclidean (extended Dynkin) diagram; hence $kQ$ is tame and representation-infinite',
    wild: 'neither Dynkin nor Euclidean; hence $kQ$ is wild'
  };

  function arProofEntries() {
    const d = arDrawn;
    const entries = [];
    const ar = d.value.ar, info = d.value.info, src = d.src, cat = d.cat, items = d.items, links = d.links;
    const n = info.verts.length;
    const lab = (a) => texEsc(vlabel(info, a));
    const vecOf = (it) => (it.kind === 'der' && cat === 'derived' ? it.nd.cls : it.dim);
    const types = src.comps.map((c) => '$' + texType(c.name) + '$').join(' and ');
    entries.push({
      title: '**Lemma.** Type of $Q$',
      lines: src.comps.map((c) => 'The underlying graph on $\\{' + c.verts.map(lab).join(',') + '\\}$ is of type $' + texType(c.name) + '$, ' + KIND_REASON[c.kind] + '.'),
      proof: false, qed: false
    });
    const listVecs = (letter, vs) => vs.map((v, i) => '$' + letter + '_{' + lab(i) + '} = ' + texVec(v) + '$').join(', ');
    entries.push({
      title: '**Lemma.** Projective and injective modules',
      lines: [
        'Since $\\operatorname{rad}P(i) = \\bigoplus_{i\\to j}P(j)$ and $I(i)/\\operatorname{soc}I(i) = \\bigoplus_{k\\to i}I(k)$, $$\\underline{\\dim}\\,P(i) = e_i + \\sum_{i\\to j}\\underline{\\dim}\\,P(j),\\qquad \\underline{\\dim}\\,I(i) = e_i + \\sum_{k\\to i}\\underline{\\dim}\\,I(k).$$',
        'Solving these recursions along $Q$: ' + listVecs('P', src.P) + '; and ' + listVecs('I', src.I) + '.'
      ],
      proof: true, qed: true
    });

    const add = (a, b) => a.map((x, t) => x + b[t]);
    const scale = (m, v) => v.map((x) => m * x);
    const same = (a, b) => a.length === b.length && a.every((x, t) => x === b[t]);
    // 带符号的数值表达式
    const expr = (terms) => {
      let out = '';
      terms.forEach(([sign, m, v], t) => {
        const neg = v.every((x) => x <= 0) && v.some((x) => x < 0);
        const sg = neg ? -sign : sign;
        const body = (m > 1 ? m + '\\cdot ' : '') + texVec(neg ? v.map((x) => -x) : v);
        out += t === 0 ? (sg < 0 ? '-' + body : body) : (sg < 0 ? ' - ' : ' + ') + body;
      });
      return out || '0';
    };
    const nameSum = (terms) => terms.map(([m, it]) => (m > 1 ? m + '\\,' : '') + it.tex).join(' + ') || '0';

    if (cat !== 'cluster') {
      const fwd = [], bwd = [];
      src.tau.forEach((t) => {
        const X = items[t.from], TX = items[t.to];
        if (!X || !TX) return;
        const forward = X.kind === 'ar' ? X.nd.kind === 'P' : TX.nd.r >= 0;
        (forward ? fwd : bwd).push({ X: X, TX: TX });
      });
      fwd.sort((a, b) => a.X.nd.r - b.X.nd.r || a.X.id - b.X.id);
      bwd.sort((a, b) => b.TX.nd.r - a.TX.nd.r || a.TX.id - b.TX.id);
      const lines = [cat === 'derived'
        ? 'An Auslander–Reiten triangle $\\tau X\\to E\\to X\\to \\tau X[1]$ gives $[X] + [\\tau X] = [E]$ in $K_0$, where $[M[d]] = (-1)^d\\,\\underline{\\dim}\\,M$. Starting from the projectives and knitting in both directions:'
        : 'An almost split sequence $0\\to\\tau X\\to E\\to X\\to 0$ gives $\\underline{\\dim}\\,X + \\underline{\\dim}\\,\\tau X = \\underline{\\dim}\\,E$, where $E$ is the sum of the middle terms of the mesh. Identifying each module with its dimension vector and starting from the projectives:'];
      const knit = (target, known, mids) => {
        let sum = vecOf(known).map((x) => -x);
        mids.forEach(([m, it]) => { sum = add(sum, scale(m, vecOf(it))); });
        const ok = same(sum, vecOf(target));
        const vals = expr(mids.map(([m, it]) => [1, m, vecOf(it)]).concat([[-1, 1, vecOf(known)]]));
        return '$' + target.tex + ' = ' + nameSum(mids) + ' - ' + known.tex + (ok ? ' = ' + vals : '') + ' = ' + texVec(vecOf(target)) + '$' +
          (ok ? '' : ' (some middle terms lie outside the range shown).');
      };
      const emitInOrder = (pairs, forward) => {
        const targetOf = (pr) => (forward ? pr.X : pr.TX);
        const midsOf = (pr) => (forward ? links.filter((e) => e.from === pr.TX.id).map((e) => [e.mult, items[e.to]])
          : links.filter((e) => e.to === pr.X.id).map((e) => [e.mult, items[e.from]]));
        const pending = new Set(pairs.map((pr) => targetOf(pr).id));
        let rest = pairs.slice();
        while (rest.length) {
          const ready = rest.filter((pr) => midsOf(pr).every(([, it]) => !pending.has(it.id) || it.id === targetOf(pr).id));
          const batch = ready.length ? ready : [rest[0]];
          batch.forEach((pr) => {
            lines.push(forward ? knit(pr.X, pr.TX, midsOf(pr)) : knit(pr.TX, pr.X, midsOf(pr)));
            pending.delete(targetOf(pr).id);
          });
          rest = rest.filter((pr) => batch.indexOf(pr) < 0);
        }
      };
      emitInOrder(fwd, true);
      emitInOrder(bwd, false);
      if (lines.length > 401) lines.splice(401, lines.length - 401, 'and so on (' + (fwd.length + bwd.length) + ' steps in total).');
      entries.push({
        title: '**Construction.** Knitting the meshes',
        lines: fwd.length || bwd.length ? lines : ['Every $P(i)$ is injective, so there is nothing to knit.'],
        proof: false, qed: false
      });

      const stops = [];
      if (cat === 'mod') {
        items.forEach((it) => {
          if (it.kind !== 'ar') return;
          if (it.nd.kind === 'P' && it.nd.inj >= 0) stops.push('$' + it.tex + '\\cong I_{' + lab(it.nd.inj) + '}$ is injective, so $\\tau^{-1}$ of it is not a module and the $\\tau$-orbit of $' + lab(it.nd.i) + '$ stops.');
          if (it.nd.kind === 'I' && it.nd.proj >= 0) stops.push('$' + it.tex + '\\cong P_{' + lab(it.nd.proj) + '}$ is projective, so the $\\tau$-orbit stops.');
        });
      } else {
        src.tau.forEach((t) => {
          const X = items[t.from], TX = items[t.to];
          if (X && TX && X.nd.deg !== TX.nd.deg) {
            stops.push('The class $[' + X.tex + '] = ' + texVec(X.nd.cls) + '$ has the opposite sign to $[' + TX.tex + ']$, so the shift changes from $[' + TX.nd.deg + ']$ to $[' + X.nd.deg + ']$.');
          }
        });
      }
      if (stops.length) {
        entries.push({
          title: cat === 'mod' ? '**Lemma.** The $\\tau$-orbits' : '**Lemma.** The shifts ($\\tau^{-1}I(j) = P(j)[1]$)',
          lines: stops, proof: false, qed: false
        });
      }

      const dyn = src.comps.every((c) => c.kind === 'dynkin');
      const main = items.filter((it) => it.kind !== 'tube');
      if (cat === 'mod') {
        const roots = src.comps.map((c) => c.count).join(' + ');
        entries.push({
          title: '**Theorem.** The Auslander–Reiten quiver of $kQ$',
          lines: dyn
            ? ['Every $\\tau^{-1}$-orbit ends at an injective module, so the preprojective component is finite; a finite component of a connected Auslander–Reiten quiver is the whole quiver (Auslander).',
               'Hence the $' + ar.total + '$ modules shown are all the indecomposables, and $' + ar.total + (src.comps.length > 1 ? ' = ' + roots : '') + '$ is the number of positive roots of ' + types + '.']
            : ['For a connected non-Dynkin quiver no $\\tau^{-r}P(i)$ is injective and no $\\tau^{r}I(i)$ is projective, so the preprojective and preinjective components are infinite and disjoint.',
               'The picture shows their first $' + ar.layers + '$ layers; every other indecomposable is regular.'],
          proof: true, qed: true
        });
      } else {
        const counts = {};
        main.forEach((it) => { counts[it.nd.deg] = (counts[it.nd.deg] || 0) + 1; });
        const per = Object.keys(counts).sort((a, b) => a - b).map((k) => '$' + counts[k] + '$ in degree $[' + k + ']$').join(', ');
        entries.push({
          title: '**Theorem** (Happel). The Auslander–Reiten quiver of $D^b(\\operatorname{mod} kQ)$',
          lines: dyn
            ? ['The objects found are ' + per + '; each degree is a copy of $\\operatorname{mod}kQ$ with $' + src.comps.map((c) => c.count).reduce((a, b) => a + b, 0) + '$ indecomposables.',
               'Hence the Auslander–Reiten quiver of $D^b(\\operatorname{mod}kQ)$ is $\\mathbb{Z}Q$.']
            : ['The component containing the projectives is $\\mathbb{Z}Q$: the preinjectives in degree $[-1]$ followed by the preprojectives in degree $[0]$.',
               'The other components are its shifts and the shifts of the regular components.'],
          proof: true, qed: true
        });
      }
    } else {
      const lines = ['Knit $\\mathbb{Z}Q$ in $D^b(\\operatorname{mod}kQ)$ as in the derived view, and identify $X$ with $F(X)$, where $F = \\tau^{-1}[1]$.',
        'Then $X[1]\\cong\\tau X$ in $\\mathcal{C}_Q$; in particular $\\tau^{-1}I(j) = P(j)[1]$ and $\\tau^{-1}(P(j)[1]) = F(P(j))\\cong P(j)$:'];
      const ids = [];
      src.tau.forEach((t) => {
        const X = items[t.from], TX = items[t.to];
        if (!X || !TX) return;
        if (X.nd.shiftP >= 0 || X.nd.ghost || (TX.nd.shiftP >= 0 && X.nd.shiftP < 0)) {
          ids.push('$\\tau^{-1}(' + TX.tex + ') = ' + X.tex + '$' + (X.nd.ghost ? ' (wrap-around)' : ''));
        }
      });
      if (ids.length) lines.push(ids.join(', ') + '.');
      const dyn = src.comps.every((c) => c.kind === 'dynkin');
      if (dyn) {
        const roots = src.comps.map((c) => c.count).reduce((a, b) => a + b, 0);
        lines.push('Hence $\\mathcal{C}_Q$ has $' + src.total + ' = ' + roots + ' + ' + n + '$ indecomposable objects: the indecomposable modules and the $P(i)[1]$.');
        lines.push('This is the number of cluster variables of the cluster algebra of type ' + types + ' (Buan–Marsh–Reineke–Reiten–Todorov).');
      } else {
        lines.push('Hence the transjective component is $\\mathbb{Z}Q$ — preinjectives, then the $P(i)[1]$, then preprojectives — and the regular components are those of $\\operatorname{mod}kQ$.');
      }
      entries.push({ title: '**Theorem.** The cluster category $\\mathcal{C}_Q = D^b(\\operatorname{mod}kQ)/\\langle\\tau^{-1}[1]\\rangle$', lines: lines, proof: true, qed: true });
    }

    // 管
    if (items.some((it) => it.kind === 'tube')) {
      src.comps.forEach((c) => {
        if (c.kind !== 'euclidean' || !c.regular || !c.regular.ok) return;
        const reg = c.regular;
        const lines = [
          'The vector $\\delta = ' + texVec(reg.delta) + '$ spans the radical of the Tits form: $q(\\delta) = 0$.',
          'A module $X$ is regular if and only if its defect $\\langle\\delta,\\underline{\\dim}\\,X\\rangle$ vanishes, and $\\underline{\\dim}\\,\\tau X = \\Phi\\,\\underline{\\dim}\\,X$ with the Coxeter transformation $\\Phi = -C E^{\\mathsf T}$.',
          'The real roots $0 < x < \\delta$ of defect $0$ fall into $\\Phi$-orbits, and an orbit whose sum is $\\delta$ consists of the regular simples of one exceptional tube: $$\\begin{aligned}' +
            reg.tubes.map((t, ti) => '\\text{tube } ' + (ti + 1) + ' \\ (\\text{rank } ' + t.rank + ')&:\\ ' + t.simples.map(texVec).join(' + ') + ' = \\delta').join('\\\\ ') + '\\end{aligned}$$',
          'Since $\\sum(\\operatorname{rank} - 1) = ' + reg.tubes.reduce((a, t) => a + t.rank - 1, 0) + ' = n - 2$ with $n = ' + c.verts.length + '$, there are no other exceptional tubes.',
          'The module $E_k[\\ell]$ has the $\\ell$ consecutive regular simples $E_k, E_{k-1}, \\dots$ as composition factors, and in a homogeneous tube $\\underline{\\dim}\\,M_\\lambda[\\ell] = \\ell\\,\\delta$.'
        ];
        entries.push({ title: '**Theorem.** Regular components of type $' + texType(c.name) + '$', lines: lines, proof: true, qed: true });
      });
    }
    return entries;
  }

  function renderARProof() {
    const list = $('ar-proof-list');
    let entries;
    if (!arDrawn) {
      const v = computeAR();
      entries = v.ar.reason === 'cyclic'
        ? [{ title: '**Remark.** No Auslander–Reiten quiver', lines: ['$Q$ has an oriented cycle, so $kQ$ is infinite-dimensional; the knitting algorithm needs an acyclic quiver.'], proof: false, qed: false }]
        : [];
    } else entries = arProofEntries();
    renderProofList(list, entries, 'Nothing to show.');
    list.scrollTop = 0;
  }

  function renderARInfo() {
    const box = $('ar-info');
    if (!arDrawn) return;
    const items = arDrawn.items, links = arDrawn.links;
    const ar = arDrawn.value.ar, info = arDrawn.value.info;
    if (arSel == null || !items[arSel]) {
      const nReg = items.filter((it) => it.kind === 'tube' && !it.ghost).length;
      const nMain = items.filter((it) => it.kind !== 'tube' && !it.ghost).length;
      box.textContent = 'Click an object for details; its direct predecessors and successors are highlighted. Shown: ' + nMain + ' ' +
        (arDrawn.cat === 'mod' ? (ar.finite ? 'indecomposable modules' : 'preprojective / preinjective modules') : 'objects') +
        (nReg ? ', plus ' + nReg + ' modules in tubes' : '') + '.';
      return;
    }
    const it = items[arSel];
    const parts = [it.name];
    if (it.kind === 'der' && it.nd.deg === 0 && it.nd.shiftP < 0) {
      if (it.nd.proj >= 0 && parts[0] !== 'P' + vlabel(info, it.nd.proj)) parts.push('P' + vlabel(info, it.nd.proj));
      if (it.nd.inj >= 0) parts.push('I' + vlabel(info, it.nd.inj));
    }
    if (it.kind === 'ar') {
      const nd = it.nd;
      if ((nd.kind === 'I' || nd.r > 0) && nd.proj >= 0) parts.push('P' + vlabel(info, nd.proj));
      if ((nd.kind === 'P' || nd.r > 0) && nd.inj >= 0) parts.push('I' + vlabel(info, nd.inj));
    }
    if (it.simple) parts.push('S' + vlabel(info, it.dim.indexOf(1)));
    const nm = (id, m) => items[id].name + (m > 1 ? sup(m) : '');
    const uniq = (arr) => arr.filter((x, i) => arr.indexOf(x) === i);
    const preds = uniq(links.filter((e) => e.to === it.id).map((e) => nm(e.from, e.mult)));
    const succs = uniq(links.filter((e) => e.from === it.id).map((e) => nm(e.to, e.mult)));
    const total = it.dim.reduce((a, b) => a + b, 0);
    box.innerHTML = '';
    const b = document.createElement('b');
    b.textContent = parts.join(' ≅ ');
    box.append(b, '  dim = ');
    const code = document.createElement('code');
    code.textContent = '(' + it.dim.join(', ') + ')';
    let where;
    if (it.kind === 'ar') where = ', component ' + ar.comps[it.nd.comp].name + (it.nd.kind === 'P' ? ' (preprojective)' : ' (preinjective)');
    else if (it.kind === 'der') {
      const nd = it.nd;
      if (arDrawn.cat === 'derived') {
        where = '; class in K₀: (' + nd.cls.join(', ') + ')' + (nd.deg ? '; the object is M[' + nd.deg + '], where M is the module with the dimension vector above' : '; a module in mod kQ');
      } else if (nd.ghost) {
        where = '; the same object as P' + vlabel(info, nd.proj) + ': τ⁻¹(P' + vlabel(info, nd.proj) + '[1]) = P' + vlabel(info, nd.proj) + ', repeated here to show the wrap-around';
      } else if (nd.shiftP >= 0) {
        where = '; the object P' + vlabel(info, nd.shiftP) + '[1] of the cluster category, corresponding to the initial cluster variable x' + vlabel(info, nd.shiftP) + ' (the vector shown is dim P' + vlabel(info, nd.shiftP) + ')';
      } else {
        where = '; an indecomposable module in the cluster category, corresponding to a non-initial cluster variable with denominator vector dim M';
      }
    }
    else if (it.tube.homog) where = ', regular, in a homogeneous tube (quasi-length ' + it.l + ', dim = ' + it.l + 'δ; one for each λ ∈ ℙ¹ outside the exceptional points)';
    else where = ', regular, in exceptional tube ' + it.tube.index + ' (rank ' + it.tube.rank + '), quasi-length ' + it.l +
      (it.l === 1 ? ' (regular simple)' : '') + (it.l % it.tube.rank === 0 ? ', dim is a multiple of δ' : '');
    box.append(code, ', total dimension ' + total + where);
    box.append(document.createElement('br'));
    box.append('Direct predecessors: ' + (preds.join(', ') || 'none') + '; direct successors: ' + (succs.join(', ') || 'none'));
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
      table.innerHTML = '<tr><td class="matrix-empty">(empty quiver)</td></tr>';
      $('matrix-caption').textContent = '';
      return;
    }
    const mut = [], frz = [];
    V.forEach((v, i) => (v.frozen ? frz : mut).push(i));
    const rows = mut.concat(frz);
    const cols = full ? rows : mut;
    $('matrix-caption').textContent = full
      ? 'Full skew-symmetric matrix (' + V.length + '×' + V.length + '); mutable vertices first, then frozen ones.'
      : 'Extended exchange matrix B̃ (' + rows.length + '×' + cols.length + '): rows = all vertices, columns = mutable vertices; the frozen rows form the coefficient part.';
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
    if (!cols.length) html += '<tr><td class="matrix-empty" colspan="2">No mutable vertices</td></tr>';
    table.innerHTML = html;
  }

  function renderStats() {
    const V = state.vertices;
    let arrows = 0, maxMult = 0;
    state.B.forEach((row) => row.forEach((x) => { if (x > 0) { arrows += x; maxMult = Math.max(maxMult, x); } }));
    const nm = V.filter((v) => !v.frozen).length;
    const items = [
      ['Vertices', V.length],
      ['Mutable', nm],
      ['Frozen', V.length - nm],
      ['Arrows', arrows],
      ['Max multiplicity', maxMult],
      ['Mutations', state.seq.length]
    ];
    $('stats').innerHTML = items.map(([k, v]) => '<dt>' + k + '</dt><dd>' + v + '</dd>').join('');
  }

  function renderSeq() {
    const log = $('seq-log');
    if (!state.seq.length) {
      log.textContent = 'No mutations yet.';
      return;
    }
    const labels = state.seq.map((id) => { const v = byId(id); return v ? v.label : '?'; });
    log.innerHTML = '';
    log.append('Applied: ');
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
    $('stage-play').textContent = playTimer ? 'Pause' : 'Play';
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
    try { localStorage.setItem(STORAGE_KEY, snapshot()); } catch (e) { /* ignore */ }
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
    try { localStorage.setItem(STORAGE_KEY + '-steps', $('opt-steps').checked ? '1' : '0'); } catch (e) { /* ignore */ }
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
  const setCollapsed = (panel, btn, c) => {
    $(panel).classList.toggle('collapsed', c);
    $(btn).textContent = c ? 'Show' : 'Hide';
    $(btn).setAttribute('aria-expanded', c ? 'false' : 'true');
    try { localStorage.setItem(STORAGE_KEY + '-' + panel, c ? '1' : '0'); } catch (e) { /* ignore */ }
  };
  [['proof', 'proof-toggle'], ['ar-proof', 'ar-proof-toggle']].forEach(([panel, btn]) => {
    let c = false;
    try { c = localStorage.getItem(STORAGE_KEY + '-' + panel) === '1'; } catch (e) { /* ignore */ }
    setCollapsed(panel, btn, c);
    $(btn).addEventListener('click', () => setCollapsed(panel, btn, !$(panel).classList.contains('collapsed')));
  });
  $('proof-clear').addEventListener('click', () => { proofEntries = []; renderProof(); });
  ['ar-label', 'ar-tau'].forEach((id) => $(id).addEventListener('change', drawAR));
  $('ar-reg').addEventListener('change', () => { arSel = null; arScale = null; drawAR(); });
  $('ar-cat').addEventListener('change', () => { arSel = null; arScale = null; drawAR(); });
  ['ar-dmin', 'ar-dmax'].forEach((id) => $(id).addEventListener('input', () => {
    if (Number.isFinite(parseInt($(id).value, 10))) { arSel = null; arScale = null; drawAR(); }
  }));
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
    if (modHL) moduleProof(kind, id);
  });
  $('matrix').addEventListener('change', (e) => {
    const t = e.target;
    if (!t.dataset || t.dataset.r == null) return;
    const v = Number(t.value);
    if (!Number.isInteger(v) || Math.abs(v) > 99) { toast('Enter an integer between −99 and 99.'); renderMatrix(); return; }
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
    let s = '# vertex order: ' + V.map((v) => v.label).join(' ') + '\n';
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
    if (!text) { toast('Nothing to import.'); return false; }
    let next = null;
    if (text[0] === '{') {
      let o;
      try { o = JSON.parse(text); } catch (e) { toast('Could not parse JSON: ' + e.message); return false; }
      if (!Array.isArray(o.vertices) || !Array.isArray(o.matrix)) { toast('The JSON is missing “vertices” or “matrix”.'); return false; }
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
      toast('The matrix must be a square ' + n + '×' + n + ' integer matrix.');
      return false;
    }
    if (new Set(next.vertices.map((v) => v.label)).size !== n) { toast('Vertex labels must be distinct.'); return false; }
    if (!Q.isSkewSymmetric(next.B)) { toast('The matrix is not skew-symmetric (need b_ij = −b_ji).'); return false; }
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
    toast(removed ? 'Imported (ignored ' + removed + ' arrow(s) between frozen vertices).' : 'Imported.');
    proof('Import', [
      'Read a $' + n + '\\times ' + n + '$ integer matrix and checked $b_{ij} = -b_{ji}$, i.e. that it is skew-symmetric.',
      'Arrows: ' + (arrowList().length ? listT(arrowList(), 10) : 'none') + '.',
      removed ? 'Ignored $' + removed + '$ arrow(s) between frozen vertices.' : ''
    ]);
    return true;
  }

  $('io-json').addEventListener('click', () => { $('io-text').value = exportJSON(); });
  $('io-tikz').addEventListener('click', () => { $('io-text').value = exportTikZ(); });
  $('io-matrix').addEventListener('click', () => { $('io-text').value = exportMatrix(); });
  $('io-copy').addEventListener('click', () => {
    const ta = $('io-text');
    const done = () => toast('Copied to clipboard.');
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
  renderProof();

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
