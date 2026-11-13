# quiver

**Try it online: <https://cosonder.github.io/quiver/>**

A browser-based tool for drawing **quivers** and **ice quivers** and exploring **quiver mutation**, path algebras and Auslander–Reiten quivers.

No build step and no dependencies: use the online version above, or open `index.html` locally in a browser.

## Features

- **Drawing quivers**: double-click an empty spot to add a vertex; with the **Arrow** tool, drag from the source to the target (or click the source, then the target) to draw an arrow. Multiple arrows are allowed; an arrow in the opposite direction cancels one (quivers have no 1-cycles or 2-cycles).
- **Ice quivers**: vertices can be frozen (drawn as squares). Frozen vertices cannot be mutated, and arrows between frozen vertices are ignored unless “Frozen arrows” is turned on (see the Λ-invariant below). One click adds **principal coefficients** (i′ → i) or **coprincipal coefficients** (i → i′).
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
- **Dynkin Hom / Ext¹ inspector**: in `mod kQ`, click a module to choose X and Shift-click to choose Y, or use the two selectors. The inspector displays the dimensions of Hom and Ext¹ in both directions and their Euler pairings. Green fill highlights modules Y with Ext¹(X,Y) = Ext¹(Y,X) = 0; directional Ext-vanishing and nonzero Hom filters are also available. The Proof panel explains the Hom-hammock recurrence and shows the selected pair's numerical calculation. Clear X / Y resets the selection.
  - Scope: path algebras without relations over an algebraically closed field, with every connected component of type A, D or E. The inspector is disabled for truncated algebras, non-Dynkin quivers and the derived / cluster category views. Computations are limited to 512 indecomposable modules.
  - Hom is computed in topological AR order from almost split sequences (with the radical inclusion at projective modules), not by counting paths. Ext¹ is recovered from `dim Hom − dim Ext¹ = Euler pairing`. Compatibility means vanishing in both directions.
- **Λ-invariant (Canesin–Cao–Janssens)**: the constructions of *Additive categorification of the monoidal Λ-invariant* ([arXiv:2605.03925](https://arxiv.org/abs/2605.03925)).
  - **Frozen arrows**: with “Frozen arrows” on, arrows between frozen vertices are kept. Frozen arrows are drawn in blue, and mutation is the extended Fomin–Zelevinsky mutation of Pressland (a path u → k → w between frozen vertices gives an unfrozen arrow; a 2-cycle of an unfrozen and a frozen arrow becomes a frozen arrow). With it off, the classical convention applies and such arrows are ignored.
  - **Compatible pair**: the Λ panel shows the Euler matrix B̂ of the ice quiver and Λ = |det B̂|·(B̂⁻ᵀ − B̂⁻¹), and checks B̃ᵀΛ = 2|det B̂|·(I | 0) (Proposition 4.1). Under mutation Λ follows μₖ(Λ) = EₖᵀΛEₖ (Proposition 4.3); this is verified at every mutation. If det B̂ ≠ ±1 the panel notes that the relative Ginzburg algebra cannot be proper (Lemma 4.4).
  - **Monoidal seed Q^[a,b](w₀)** (§5.3): from a Dynkin type A/D/E, a reduced word of the longest element (adapted to a chosen orientation, or typed in and checked) and an interval [a, b], the page builds the initial seed of Kashiwara–Kim–Oh–Park with its frozen vertices, frozen arrows and potential, and reports whether properness is known (Theorem C, Proposition 8.19) or conjectural (Conjecture 8.1).
  - **Theorem D**: for an adapted word the vertices are labelled by Kirillov–Reshetikhin modules W^(i)_{r,q^p}, and the entries of Λ are their Λ-invariants. Theorem A (λᵢⱼ = [Mᵢ, Mⱼ]_H) is quoted whenever properness is known.
  - What is computed is the combinatorial side (B̂, Λ, the quiver, the labels). The Higgs category, its Ext groups and properness itself are not computed; the theorems of the paper are cited for them.
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
- `lambda-core.js`: Euler matrix, compatible pair, mutation of ice quivers with frozen arrows, Dynkin/Weyl-group data and the quiver Q^[a,b](w₀)
- `ar-core.js`: AR quivers (knitting, classification, tubes of the regular components, derived and cluster categories, layout)
- `vendor/katex/`: KaTeX 0.16.11 (MIT license), used to typeset the proofs; bundled so the page also works offline
- `tests/core.test.js`, `tests/ar.test.js`, `tests/hom.test.js`, `tests/lambda.test.js`: tests; run `node tests/core.test.js && node tests/ar.test.js && node tests/hom.test.js && node tests/lambda.test.js`. The Λ tests check Propositions 4.1 and 4.3 and Lemma 4.2 on random ice quivers, Example 5.6 of the paper, det B̂ = ±1 for the quivers Q^[a,b](w₀), the Hernandez–Leclerc description of the adapted case (Lemma 5.10), and Theorem D for sl₂ against the monoidal side (q-strings). Hom/Ext tests include independent linear-equation oracles for every orientation of A₁–A₆ and D₄, plus D/E identities and unsupported-input checks.
