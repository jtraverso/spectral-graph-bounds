/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

import Solution
import Mathlib.Algebra.BigOperators.Fin

open Finset GraphCheeger

#print axioms AdjacencySpectrum.average_degree_le
#print axioms AdjacencySpectrum.le_maxDegree
#print axioms AdjacencySpectrum.wilf
#print axioms AdjacencySpectrum.hoffman_chromatic
#print axioms AdjacencySpectrum.hoffman_ratio
#print axioms GraphCheeger.cheeger_inequalities
#print axioms GraphCheeger.poincare
#print axioms GraphCheeger.le_gap_iff
#print axioms GraphCheeger.spectral_cut_bound
#print axioms GraphCheeger.energy_eq_laplacian
#print axioms GraphCheeger.gap_le_laplacian_eigenvalue

namespace Audit

noncomputable section

abbrev K2 := (⊤ : SimpleGraph (Fin 2))

-- The cut has one undirected edge; the arc set has both orientations.
example : boundary K2 {0} = 1 := by
  rw [boundary_singleton]
  simp [SimpleGraph.complete_graph_degree]

example : (arcs K2).card = 2 := by decide

-- Check the normalization of energy and the mean-zero constraint on two vertices.
lemma k2_energy (f : Fin 2 → ℝ) (hf : (∑ x, f x) = 0) : energy K2 f = 2 * mass f := by
  have hz : f 1 = - f 0 := by
    simp only [Fin.sum_univ_two] at hf
    linarith
  rw [energy, sum_arcs]
  simp [K2, SimpleGraph.top_adj, Fin.sum_univ_two, mass, hz]
  ring

lemma k2_cheeger : cheegerConstant K2 = 1 := by
  apply le_antisymm
  · have h := cheeger_le_maxDegree K2 (by decide)
    simpa using h
  · apply le_csInf (cuts_nonempty K2 (by decide))
    rintro r ⟨A, hpos, hhalf, rfl⟩
    have hc : A.card = 1 := by simp only [Fintype.card_fin] at hhalf; omega
    obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hc
    rw [boundary_singleton]
    have hd := SimpleGraph.IsRegularOfDegree.top (V := Fin 2) v
    simp only [Fintype.card_fin] at hd
    rw [hd]
    norm_num

-- The easy Cheeger direction is attained exactly: lambda = 2, h = 1.
lemma k2_gap : spectralGap K2 = 2 := by
  apply le_antisymm
  · have h := (cheeger_inequalities K2 (by decide)).1
    rw [k2_cheeger] at h
    linarith
  · apply (le_gap_iff K2 (by decide) 2).mpr
    intro f hf
    exact (k2_energy f hf).ge

example : spectralGap K2 / 2 = cheegerConstant K2 := by rw [k2_gap, k2_cheeger]; norm_num

-- Disconnected edgeless graph: the actual expansion and variational gap are both zero.
example : cheegerConstant (⊥ : SimpleGraph (Fin 3)) = 0 ∧
    spectralGap (⊥ : SimpleGraph (Fin 3)) = 0 := by
  let G := (⊥ : SimpleGraph (Fin 3))
  have hc : cheegerConstant G = 0 := by
    have h := cheeger_le_maxDegree G (by decide)
    rw [SimpleGraph.maxDegree_bot_eq_zero] at h
    exact le_antisymm (by simpa using h) (cheeger_nonneg G (by decide))
  refine ⟨hc, ?_⟩
  have h := (cheeger_inequalities G (by decide)).1
  rw [hc] at h
  exact le_antisymm (by linarith) (gap_nonneg G (by decide))

end
end Audit
