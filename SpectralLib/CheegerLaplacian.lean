/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import SpectralLib.CheegerVariational
public import Mathlib.Combinatorics.SimpleGraph.LapMatrix

/-! # Connection with Mathlib's combinatorial graph Laplacian -/

@[expose] public section

noncomputable section

namespace GraphCheeger

open Finset Matrix

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The evaluation-space energy is the quadratic form of Mathlib's actual Laplacian. -/
theorem energy_eq_laplacian (f : V → ℝ) :
    energy G f = f ⬝ᵥ (G.lapMatrix ℝ *ᵥ f) := by
  rw [← Matrix.toLinearMap₂'_apply', G.lapMatrix_toLinearMap₂' (R := ℝ)]
  exact congrArg (fun x : ℝ => x / 2) (sum_arcs G _)

theorem sum_laplacian (f : V → ℝ) : (∑ x, (G.lapMatrix ℝ *ᵥ f) x) = 0 := by
  have hsym : (G.lapMatrix ℝ)ᵀ = G.lapMatrix ℝ := G.isSymm_lapMatrix ℝ
  have h : (1 : V → ℝ) ⬝ᵥ (G.lapMatrix ℝ *ᵥ f) =
      f ⬝ᵥ (G.lapMatrix ℝ *ᵥ (1 : V → ℝ)) := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hsym, dotProduct_comm]
  rw [G.lapMatrix_mulVec_one_eq_zero (R := ℝ)] at h
  simpa [dotProduct] using h

/-- Every nonzero eigenvalue of the graph Laplacian is at least the variational gap. -/
theorem gap_le_laplacian_eigenvalue (l : ℝ) (hl : l ≠ 0) (f : V → ℝ) (hf : f ≠ 0)
    (heig : G.lapMatrix ℝ *ᵥ f = l • f) : spectralGap G ≤ l := by
  have hsum := sum_laplacian G f
  rw [heig] at hsum
  simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum] at hsum
  have hzero : (∑ x, f x) = 0 := (mul_eq_zero.mp hsum).resolve_left hl
  have hmass : 0 < mass f := by
    apply lt_of_le_of_ne (mass_nonneg f)
    intro hz
    apply hf
    funext x
    have hs : ∑ x, f x ^ 2 = 0 := hz.symm
    have hx := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => sq_nonneg (f x))).mp hs x (mem_univ x)
    exact (sq_eq_zero_iff).mp hx
  have he : energy G f = l * mass f := by
    rw [energy_eq_laplacian, heig, dotProduct_smul, smul_eq_mul]
    simp only [mass, dotProduct, sq]
  have h := gap_le_rayleigh G f hzero hmass
  rw [he, mul_div_cancel_right₀ _ hmass.ne'] at h
  exact h

end GraphCheeger
