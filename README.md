# quiver

**Try it online: <https://cosonder.github.io/quiver/>**

A browser-based tool for drawing **quivers** and **ice quivers** and exploring **quiver mutation**, path algebras and Auslander–Reiten quivers.

No build step and no dependencies: use the online version above, or open `index.html` locally in a browser.

## Features

- **Drawing quivers**: double-click an empty spot to add a vertex; with the **Arrow** tool, drag from the source to the target (or click the source, then the target) to draw an arrow. Multiple arrows are allowed; an arrow in the opposite direction cancels one (quivers have no 1-cycles or 2-cycles).
- **Ice quivers**: vertices can be frozen (drawn as squares). Frozen vertices cannot be mutated, and arrows between frozen vertices are ignored. One click adds **principal coefficients** (i → i′) or **coprincipal coefficients** (i′ → i).
- **Mutation μₖ**: click a vertex to mutate; run a mutation sequence (e.g. `1 2 1`), mutate at random, go back to the initial seed, undo/redo.
- **Step-by-step mode**: shows a mutation in three animated steps: compose paths i → k → j, reverse the arrows incident to k, remove 2-cycles (and arrows between frozen vertices).
- **Exchange matrix**: the extended exchange matrix B̃ (or the full skew-symmetric matrix) is shown live and can be edited directly.
- **Path algebra**: the dimension of the path algebra kQ (infinite if Q has an oriented cycle; the truncation kQ/R^L is available instead), and the dimension vectors and dimensions of the indecomposable projectives P(i), injectives I(i) and simples S(i). A module's dimension vector can be shown on the canvas, together with the radical layers of P(i) or the socle layers of I(i).
- **Auslander–Reiten quiver**: for the path algebra kQ of an acyclic quiver, the AR quiver is computed by knitting, and each component of the underlying graph is classified as Dynkin, Euclidean or wild.
  - Dynkin types (A/D/E): all indecomposable modules (as many as positive roots).
  - Euclidean types: also the regular components. The exceptional tubes are found from the null root δ, the defect and the Coxeter transformation; their ranks agree with the known values (Ã_{p,q}: p, q; D̃ₙ: 2, 2, n−2; Ẽ₆/₇/₈: 2,3,3 / 2,3,4 / 2,3,5). A homogeneous tube is drawn as well.
  - Wild types: the first layers of the preprojective and preinjective components (the regular components, infinitely many of type ℤA∞, are not drawn).
  - Labels can be dimension vectors or τ-orbit names. Clicking a module shows its dimension vector, the projective / injective / simple module it is isomorphic to, and its direct predecessors and successors.
- **AR quivers of the derived and cluster categories**: switch the category in the AR quiver window.
  - D^b(mod kQ): following Happel's theorem, ℤQ is knitted with signed classes in K₀ (τ⁻¹I(j) = P(j)[1]). For Dynkin types a range of shifts [a, b] can be chosen; for other types, the component containing the projectives (preinjectives[−1] ∪ preprojectives) is drawn, together with the tubes in degree [0].
  - Cluster category C_Q = D^b/τ⁻¹[1]: for Dynkin types, all indecomposable objects (indecomposable modules and the P(i)[1]; positive roots + n of them, in bijection with the cluster variables), with the wrap-around τ⁻¹(P(i)[1]) = P(i) marked; for other types, the transjective component … → I → P[1] → P → … together with the tubes.
- **Proof panel**: a panel in the bottom-right corner explains every step that changes the picture. Proofs are written in LaTeX and typeset with KaTeX in Computer Modern, in the style of a LaTeX document (amsthm-like headings, *Proof.*, □).
  - Each edit is explained in terms of the matrix B (e.g. drawing an arrow sets b[i,j] and b[j,i] by skew-symmetry).
  - Each mutation μₖ is derived through the three steps (compose, reverse, cancel), then checked entry by entry against the matrix formula.
  - Highlighting a module's dimension vector shows the count of paths by length.
  - The AR quiver window has its own Proof panel: the classification, the projectives and injectives, every mesh computation (τ⁻¹X = Σ middle terms − X), where each τ-orbit stops or the shift changes, the derivation of the tubes, and the identifications in the cluster category.
- **Examples**: A₃, A₄, D₄, E₆, D̃₄, Ã₂, an oriented 3-cycle, the Kronecker and Markov quivers, A₂/A₃ with principal coefficients, and the ice quivers of Gr(2,5) and Gr(2,6).
- **Import / export**: JSON, skew-symmetric matrix text, and TikZ code.

## Mutation rule

At a mutable vertex k:

```
b'_ij = -b_ij                                  if i = k or j = k
b'_ij = b_ij + (|b_ik| b_kj + b_ik |b_kj|) / 2  otherwise
```

In an ice quiver, b'_ij is always 0 between frozen vertices.

## Path algebra conventions

In the language of quiver representations: P(i)_j has a basis of the paths from i to j, I(i)_j has a basis of the paths from j to i, and S(i) is k at vertex i and 0 elsewhere. The number of paths of length l from i to j is (A^l)_ij, where A is the arrow-count matrix. For ice quivers the frozen vertices are included by default; you can restrict to the mutable part instead.

## Files

- `index.html`, `style.css`, `app.js`: page and interaction
- `quiver-core.js`: mathematical core for mutation and path algebras (works in the browser and in Node)
- `ar-core.js`: AR quivers (knitting, classification, tubes of the regular components, derived and cluster categories, layout)
- `vendor/katex/`: KaTeX 0.16.11 (MIT license), used to typeset the proofs; bundled so the page also works offline
- `tests/core.test.js`, `tests/ar.test.js`: tests; run `node tests/core.test.js && node tests/ar.test.js`
