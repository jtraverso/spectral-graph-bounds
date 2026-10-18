/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import SpectralLib.SpectralBounds

/-!
# Proofs of the statements in `Challenge.lean`

The theorems are proved in `SpectralLib/SpectralBounds.lean` (namespace `SpectralBounds`) from
Mathlib's spectral theorem for Hermitian matrices: expanding the quadratic form of `A` in an
orthonormal eigenbasis gives the Rayleigh bounds `λ_min ‖x‖² ≤ xᵀAx ≤ λ_max ‖x‖²`. The average
degree bound takes `x = 1`; the maximum degree bound looks at the largest coordinate (in absolute
value) of a unit eigenvector for `λ_max`. For Wilf's theorem, testing the quadratic form on the
indicator vector of any vertex set `S` gives a vertex with at most `λ_max` neighbours in `S`, so
a greedy colouring uses at most `⌊λ_max⌋ + 1` colours. Both Hoffman bounds apply the Rayleigh
lower bound to vectors combining an eigenvector with vectors supported on independent sets
(the colour classes, respectively the given independent set).
-/

@[expose] public section

open Finset SimpleGraph

namespace AdjacencySpectrum

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V)
  [DecidableRel G.Adj] (hA : (G.adjMatrix ℝ).IsHermitian)

/-- The average degree `2 |E| / n` is at most the largest adjacency eigenvalue. -/
theorem average_degree_le :
    2 * (#G.edgeFinset : ℝ) / Fintype.card V ≤ ⨆ i, hA.eigenvalues i :=
  SpectralBounds.average_degree_le G hA

/-- The largest adjacency eigenvalue is at most the maximum degree. -/
theorem le_maxDegree : ⨆ i, hA.eigenvalues i ≤ G.maxDegree :=
  SpectralBounds.le_maxDegree G hA

/-- **Wilf's theorem (1967).** A finite graph is `(⌊λ_max⌋ + 1)`-colourable, where `λ_max` is
the largest eigenvalue of its adjacency matrix. -/
theorem wilf : G.Colorable (⌊⨆ i, hA.eigenvalues i⌋₊ + 1) :=
  SpectralBounds.wilf G hA

/-- **Hoffman's bound (1970).** If a finite graph has at least one edge, every proper colouring
with `c` colours satisfies `1 - λ_max / λ_min ≤ c`. -/
theorem hoffman_chromatic (hE : G.edgeSet.Nonempty) {c : ℕ} (hc : G.Colorable c) :
    1 - (⨆ i, hA.eigenvalues i) / (⨅ i, hA.eigenvalues i) ≤ c :=
  SpectralBounds.hoffman_chromatic G hA hE hc

/-- **Hoffman's ratio bound.** If a finite graph is `k`-regular with `k ≥ 1`, every independent
set has at most `n (−λ_min) / (k − λ_min)` vertices. -/
theorem hoffman_ratio {k : ℕ} (hk : 1 ≤ k) (hreg : G.IsRegularOfDegree k) {s : Finset V}
    (hs : G.IsIndepSet (s : Set V)) :
    (#s : ℝ) ≤ Fintype.card V * (-(⨅ i, hA.eigenvalues i)) / (k - ⨅ i, hA.eigenvalues i) :=
  SpectralBounds.hoffman_ratio G hA hk hreg hs

end AdjacencySpectrum
