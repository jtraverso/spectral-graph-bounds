/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# Spectral bounds on the chromatic number and the independence number

Let `G` be a finite simple graph on a nonempty vertex type, `A` its real adjacency matrix
(Mathlib's `SimpleGraph.adjMatrix`), which is Hermitian, and `λ_max`, `λ_min` its largest and
smallest eigenvalues (`Matrix.IsHermitian.eigenvalues`).

* `AdjacencySpectrum.average_degree_le` and `AdjacencySpectrum.le_maxDegree`: the average degree
  `2|E|/n` is at most `λ_max`, and `λ_max` is at most the maximum degree.
* `AdjacencySpectrum.wilf`: **Wilf (1967).** `G` is `(⌊λ_max⌋ + 1)`-colourable.
* `AdjacencySpectrum.hoffman_chromatic`: **Hoffman (1970).** If `G` has an edge, every proper
  colouring uses at least `1 - λ_max / λ_min` colours.
* `AdjacencySpectrum.hoffman_ratio`: **Hoffman's ratio bound.** If `G` is `k`-regular with `k ≥ 1`,
  every independent set has at most `n (−λ_min) / (k − λ_min)` vertices.

The Mathlib definitions used in these statements are reproduced verbatim, with file and line at the
pinned Mathlib revision, in `MATHLIB_DEFINITIONS.md` at the root of this repository.
-/

@[expose] public section

open Finset SimpleGraph

namespace AdjacencySpectrum

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V)
  [DecidableRel G.Adj] (hA : (G.adjMatrix ℝ).IsHermitian)

/-- The average degree `2 |E| / n` is at most the largest adjacency eigenvalue. -/
theorem average_degree_le :
    2 * (#G.edgeFinset : ℝ) / Fintype.card V ≤ ⨆ i, hA.eigenvalues i := by
  sorry

/-- The largest adjacency eigenvalue is at most the maximum degree. -/
theorem le_maxDegree : ⨆ i, hA.eigenvalues i ≤ G.maxDegree := by
  sorry

/-- **Wilf's theorem (1967).** A finite graph is `(⌊λ_max⌋ + 1)`-colourable, where `λ_max` is
the largest eigenvalue of its adjacency matrix. -/
theorem wilf : G.Colorable (⌊⨆ i, hA.eigenvalues i⌋₊ + 1) := by
  sorry

/-- **Hoffman's bound (1970).** If a finite graph has at least one edge, every proper colouring
with `c` colours satisfies `1 - λ_max / λ_min ≤ c`. -/
theorem hoffman_chromatic (hE : G.edgeSet.Nonempty) {c : ℕ} (hc : G.Colorable c) :
    1 - (⨆ i, hA.eigenvalues i) / (⨅ i, hA.eigenvalues i) ≤ c := by
  sorry

/-- **Hoffman's ratio bound.** If a finite graph is `k`-regular with `k ≥ 1`, every independent
set has at most `n (−λ_min) / (k − λ_min)` vertices. -/
theorem hoffman_ratio {k : ℕ} (hk : 1 ≤ k) (hreg : G.IsRegularOfDegree k) {s : Finset V}
    (hs : G.IsIndepSet (s : Set V)) :
    (#s : ℝ) ≤ Fintype.card V * (-(⨅ i, hA.eigenvalues i)) / (k - ⨅ i, hA.eigenvalues i) := by
  sorry

end AdjacencySpectrum
