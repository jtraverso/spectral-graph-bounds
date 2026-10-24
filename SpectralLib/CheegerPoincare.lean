/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import SpectralLib.CheegerCoarea

/-! # CheegerPoincare
Finite graph expansion and variational spectral estimates. -/

@[expose] public section

noncomputable section

namespace GraphCheeger

open Finset CheegerPoincare

universe u
variable {V : Type u} [Fintype V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

open Classical in
theorem variation_nonneg (f : V → ℝ) : 0 ≤ variation G f := by
  exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)

open Classical in
theorem sum_arcs_first (f : V → ℝ) :
    (∑ e ∈ arcs G, f e.1 ^ 2) = ∑ x, (G.degree x : ℝ) * f x ^ 2 := by
  rw [sum_arcs]
  apply Finset.sum_congr rfl
  intro x _
  have hd : (G.degree x : ℝ) = ∑ y : V, if G.Adj x y then 1 else 0 := by
    unfold SimpleGraph.degree SimpleGraph.neighborFinset SimpleGraph.neighborSet
    rw [Finset.sum_boole, Set.toFinset_ofPred]
  rw [hd, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro y _
  split_ifs <;> simp

open Classical in
theorem sum_arcs_first_le (f : V → ℝ) :
    (∑ e ∈ arcs G, f e.1 ^ 2) ≤ G.maxDegree * mass f := by
  rw [sum_arcs_first, mass, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact_mod_cast G.degree_le_maxDegree x

open Classical in
theorem square_variation_bound (f : V → ℝ) :
    variation G (fun x => f x ^ 2) ^ 2 ≤ 8 * G.maxDegree * energy G f * mass f := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (arcs G)
    (fun e => |f e.1 - f e.2|) (fun e => |f e.1 + f e.2|)
  have hprod : (∑ e ∈ arcs G, |f e.1 - f e.2| * |f e.1 + f e.2|) =
      variation G (fun x => f x ^ 2) := by
    apply Finset.sum_congr rfl
    intro e _
    rw [← abs_mul]
    congr 1
    ring
  have hdiff : (∑ e ∈ arcs G, |f e.1 - f e.2| ^ 2) = 2 * energy G f := by
    simp only [sq_abs]
    unfold energy
    ring
  have hplus : (∑ e ∈ arcs G, |f e.1 + f e.2| ^ 2) ≤ 4 * G.maxDegree * mass f := by
    calc
      _ ≤ ∑ e ∈ arcs G, (2 * f e.1 ^ 2 + 2 * f e.2 ^ 2) := by
        apply Finset.sum_le_sum
        intro e _
        rw [sq_abs]
        nlinarith [sq_nonneg (f e.1 - f e.2)]
      _ = 4 * ∑ e ∈ arcs G, f e.1 ^ 2 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
          sum_arcs_swap G (fun e => f e.1 ^ 2)]
        ring
      _ ≤ _ := by
        have h := sum_arcs_first_le G f
        linarith
  rw [hprod, hdiff] at hcs
  have hscale := mul_le_mul_of_nonneg_left hplus (show 0 ≤ 2 * energy G f by have he := energy_nonneg G f; positivity)
  nlinarith only [hcs, hscale]

open Classical in
theorem small_support_poincare (h : ℝ) (hh : 0 ≤ h)
    (hexp : ∀ A : Finset V, 2 * A.card ≤ Fintype.card V → h * A.card ≤ boundary G A)
    (f : V → ℝ) (hf : ∀ x, 0 ≤ f x)
    (hhalf : 2 * (positiveSupport f).card ≤ Fintype.card V) :
    h ^ 2 * mass f ≤ 2 * G.maxDegree * energy G f := by
  have hs : positiveSupport (fun x => f x ^ 2) = positiveSupport f := by
    ext x
    simp only [mem_positiveSupport]
    constructor
    · intro hx
      exact lt_of_le_of_ne (hf x) (by intro heq; simp [← heq] at hx)
    · intro hx
      positivity
  have hc := small_support_coarea G h hexp (fun x => f x ^ 2)
    (fun x => sq_nonneg _) (by simpa only [hs] using hhalf)
  change 2 * h * mass f ≤ _ at hc
  have hnonneg : 0 ≤ 2 * h * mass f := by have hs := mass_nonneg f; positivity
  have hsq : (2 * h * mass f) ^ 2 ≤ variation G (fun x => f x ^ 2) ^ 2 :=
    (sq_le_sq₀ hnonneg (variation_nonneg G _)).mpr hc
  have hbound := square_variation_bound G f
  by_cases hz : mass f = 0
  · rw [hz, mul_zero]
    have he := energy_nonneg G f
    positivity
  · have hpos : 0 < mass f := lt_of_le_of_ne (mass_nonneg f) (Ne.symm hz)
    have hmul : mass f * (h ^ 2 * mass f) ≤ mass f * (2 * G.maxDegree * energy G f) := by
      nlinarith only [hsq, hbound]
    exact le_of_mul_le_mul_left hmul hpos

open Classical in
theorem positive_negative_energy (f : V → ℝ) (m : ℝ) :
    energy G (fun x => max (f x - m) 0) + energy G (fun x => max (m - f x) 0) ≤
      energy G f := by
  unfold energy
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro e _
  dsimp only
  rcases le_total m (f e.1) with hx | hx <;> rcases le_total m (f e.2) with hy | hy
  · rw [max_eq_left (sub_nonneg.mpr hx), max_eq_left (sub_nonneg.mpr hy),
      max_eq_right (sub_nonpos.mpr hx), max_eq_right (sub_nonpos.mpr hy)]
    nlinarith only
  · rw [max_eq_left (sub_nonneg.mpr hx), max_eq_right (sub_nonpos.mpr hy),
      max_eq_right (sub_nonpos.mpr hx), max_eq_left (sub_nonneg.mpr hy)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hy)]
  · rw [max_eq_right (sub_nonpos.mpr hx), max_eq_left (sub_nonneg.mpr hy),
      max_eq_left (sub_nonneg.mpr hx), max_eq_right (sub_nonpos.mpr hy)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hy)]
  · rw [max_eq_right (sub_nonpos.mpr hx), max_eq_right (sub_nonpos.mpr hy),
      max_eq_left (sub_nonneg.mpr hx), max_eq_left (sub_nonneg.mpr hy)]
    nlinarith only

open Classical in
/-- The Cheeger–Poincaré inequality, prior to taking a Rayleigh infimum. -/
theorem poincare_of_expansion [Nonempty V] (h : ℝ) (hh : 0 ≤ h)
    (hexp : ∀ A : Finset V, 2 * A.card ≤ Fintype.card V → h * A.card ≤ boundary G A)
    (f : V → ℝ) (hzero : (∑ x, f x) = 0) :
    h ^ 2 * mass f ≤ 2 * G.maxDegree * energy G f := by
  classical
  obtain ⟨m, hbelow, habove⟩ := exists_finite_real_median f
  let p : V → ℝ := fun x => max (f x - m) 0
  let q : V → ℝ := fun x => max (m - f x) 0
  have hp := small_support_poincare G h hh hexp p (fun x => le_max_right _ _)
    (by simpa only [p, positiveSupport_max_sub] using habove)
  have hq := small_support_poincare G h hh hexp q (fun x => le_max_right _ _)
    (by simpa only [q, positiveSupport_max_sub_reverse] using hbelow)
  have hmass : mass p + mass q = ∑ x, (f x - m) ^ 2 := by
    rw [mass, mass, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    rcases le_total m (f x) with hx | hx
    · simp only [p, q, max_eq_left (sub_nonneg.mpr hx), max_eq_right (sub_nonpos.mpr hx)]
      ring
    · simp only [p, q, max_eq_right (sub_nonpos.mpr hx), max_eq_left (sub_nonneg.mpr hx)]
      ring
  have hm : finiteMean f = 0 := by simp [finiteMean, hzero]
  have hmin := sum_sq_sub_finiteMean_le f m
  simp only [hm, sub_zero] at hmin
  have hmassle : mass f ≤ mass p + mass q := by rw [hmass]; exact hmin
  have he := positive_negative_energy G f m
  have hdeg : (0 : ℝ) ≤ 2 * G.maxDegree := by positivity
  have he' := mul_le_mul_of_nonneg_left he hdeg
  have hs := mul_le_mul_of_nonneg_left hmassle (sq_nonneg h)
  change _ ≤ 2 * G.maxDegree * energy G f at he'
  nlinarith only [hp, hq, hs, he']

end GraphCheeger
