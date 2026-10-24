/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini

The support-peeling induction adapts the additive coarea proof of OpenAI and
Dean Cureton, LeanPool/NonSoficGroup/Compression.lean. See THIRD_PARTY.md.
-/
module

public import SpectralLib.CheegerDefinitions

/-! # CheegerCoarea
Finite graph expansion and variational spectral estimates. -/

@[expose] public section

noncomputable section

namespace GraphCheeger

open Finset CheegerPoincare

universe u
variable {V : Type u} [Fintype V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

open Classical in
theorem sum_crossing (A : Finset V) (m : ℝ) :
    (∑ e ∈ arcs G, if e.1 ∈ A ∧ e.2 ∉ A then m else 0) = m * boundary G A := by
  classical
  calc
    _ = m * ∑ e ∈ arcs G, if e.1 ∈ A ∧ e.2 ∉ A then (1 : ℝ) else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _
      split_ifs <;> simp
    _ = _ := by rw [Finset.sum_boole]; rfl

open Classical in
theorem sum_entering (A : Finset V) (m : ℝ) :
    (∑ e ∈ arcs G, if e.1 ∉ A ∧ e.2 ∈ A then m else 0) = m * boundary G A := by
  classical
  have h := sum_arcs_swap G (fun e => if e.1 ∈ A ∧ e.2 ∉ A then m else 0)
  simpa only [and_comm, sum_crossing] using h

open Classical in
theorem variation_subtract_layer (f : V → ℝ) (A : Finset V) (m : ℝ)
    (hm : 0 ≤ m) (hinside : ∀ x ∈ A, m ≤ f x) (houtside : ∀ x, x ∉ A → f x = 0) :
    variation G f = variation G (fun x => if x ∈ A then f x - m else 0) +
      2 * m * boundary G A := by
  classical
  let g : V → ℝ := fun x => if x ∈ A then f x - m else 0
  have hpair (x y : V) :
      |f x - f y| = |g x - g y| +
        (if x ∈ A ∧ y ∉ A then m else 0) +
        (if x ∉ A ∧ y ∈ A then m else 0) := by
    by_cases hx : x ∈ A <;> by_cases hy : y ∈ A
    · simp [g, hx, hy]
    · have hy0 := houtside y hy
      have hx0 : 0 ≤ f x := hm.trans (hinside x hx)
      simp [g, hx, hy, hy0, abs_of_nonneg hx0,
        abs_of_nonneg (sub_nonneg.mpr (hinside x hx))]
    · have hx0 := houtside x hx
      have hy0 : 0 ≤ f y := hm.trans (hinside y hy)
      simp [g, hx, hy, hx0, abs_of_nonneg hy0,
        abs_of_nonpos (sub_nonpos.mpr (hinside y hy))]
    · simp [g, hx, hy, houtside x hx, houtside y hy]
  unfold variation
  calc
    _ = ∑ e ∈ arcs G, (|g e.1 - g e.2| +
        (if e.1 ∈ A ∧ e.2 ∉ A then m else 0) +
        (if e.1 ∉ A ∧ e.2 ∈ A then m else 0)) :=
      Finset.sum_congr rfl (fun e _ => hpair e.1 e.2)
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, sum_crossing, sum_entering]
      ring

open Classical in
/-- The finite coarea inequality for a nonnegative function supported on at most half the vertices. -/
theorem small_support_coarea (h : ℝ)
    (hexp : ∀ A : Finset V, 2 * A.card ≤ Fintype.card V → h * A.card ≤ boundary G A)
    (f : V → ℝ) (hf : ∀ x, 0 ≤ f x)
    (hhalf : 2 * (positiveSupport f).card ≤ Fintype.card V) :
    2 * h * (∑ x, f x) ≤ variation G f := by
  classical
  generalize hn : (positiveSupport f).card = n
  induction n using Nat.strong_induction_on generalizing f with
  | h n ih =>
    by_cases hnonempty : (positiveSupport f).Nonempty
    · let A := positiveSupport f
      have hA : A.Nonempty := hnonempty
      have himage : (A.image f).Nonempty := Finset.image_nonempty.mpr hA
      let m := (A.image f).min' himage
      obtain ⟨z, hzA, hzm⟩ := Finset.mem_image.mp (Finset.min'_mem (A.image f) himage)
      change f z = m at hzm
      have hmpos : 0 < m := by
        rw [← hzm]
        exact (mem_positiveSupport f z).mp hzA
      have hmle : ∀ x ∈ A, m ≤ f x := by
        intro x hx
        exact Finset.min'_le (A.image f) (f x) (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
      let g : V → ℝ := fun x => if x ∈ A then f x - m else 0
      have hgnonnegative : ∀ x, 0 ≤ g x := by
        intro x
        by_cases hx : x ∈ A
        · simpa [g, hx] using sub_nonneg.mpr (hmle x hx)
        · simp [g, hx]
      have hgsub : positiveSupport g ⊆ A := by
        intro x hx
        have hpositive := (mem_positiveSupport g x).mp hx
        by_contra hxA
        simp [g, hxA] at hpositive
      have hznot : z ∉ positiveSupport g := by
        intro hz
        have hpositive := (mem_positiveSupport g z).mp hz
        have hzero : g z = 0 := by simp [g, hzA, hzm]
        simp [hzero] at hpositive
      have hstrict : positiveSupport g ⊂ A := by
        apply Finset.ssubset_iff_subset_ne.mpr
        exact ⟨hgsub, fun heq => hznot (heq.symm ▸ hzA)⟩
      have hgcard : (positiveSupport g).card < n := by
        rw [← hn]
        exact Finset.card_lt_card hstrict
      have hghalf : 2 * (positiveSupport g).card ≤ Fintype.card V :=
        (Nat.mul_le_mul_left 2 (Finset.card_le_card hgsub)).trans hhalf
      have hgbound := ih (positiveSupport g).card hgcard g hgnonnegative hghalf rfl
      have hcut := hexp A hhalf
      have houtside : ∀ x, x ∉ A → f x = 0 := by
        intro x hx
        have hnot : ¬ 0 < f x := fun hp => hx ((mem_positiveSupport f x).mpr hp)
        exact le_antisymm (le_of_not_gt hnot) (hf x)
      have hsum : (∑ x, f x) = (∑ x, g x) + m * A.card := by
        calc
          _ = ∑ x, (g x + if x ∈ A then m else 0) := by
            apply Finset.sum_congr rfl
            intro x _
            by_cases hx : x ∈ A
            · simp [g, hx]
            · simp [g, hx, houtside x hx]
          _ = _ := by simp [Finset.sum_add_distrib, mul_comm]
      have hv := variation_subtract_layer G f A m hmpos.le hmle houtside
      have hscaled := mul_le_mul_of_nonneg_left hcut (show 0 ≤ 2 * m by positivity)
      rw [hsum, hv]
      nlinarith only [hgbound, hscaled]
    · have hzero : ∀ x, f x = 0 := by
        intro x
        have hx : ¬ 0 < f x := fun hp => hnonempty ⟨x, (mem_positiveSupport f x).mpr hp⟩
        exact le_antisymm (le_of_not_gt hx) (hf x)
      simp [hzero, variation]

end GraphCheeger
