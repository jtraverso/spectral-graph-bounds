/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: OpenAI, Dean Cureton

Extracted and adapted from LeanPool/NonSoficGroup/Foundations.lean,
commit edbe5bd56f476cc2965564676b66199f281ab714. See THIRD_PARTY.md.
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! # Median
Finite graph expansion and variational spectral estimates. -/

@[expose] public section

noncomputable section

namespace CheegerPoincare

open scoped BigOperators

/-- Internal interface connecting the split non-sofic proof modules. -/
noncomputable def positiveSupport {V : Type*} [Fintype V]
    (f : V → ℝ) : Finset V := by
  classical
  exact Finset.univ.filter fun x => 0 < f x

@[simp] theorem mem_positiveSupport {V : Type*} [Fintype V]
    (f : V → ℝ) (x : V) :
    x ∈ positiveSupport f ↔ 0 < f x := by
  classical
  simp only [positiveSupport, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Internal interface connecting the split non-sofic proof modules. -/
noncomputable def finiteMean {V : Type*} [Fintype V] (f : V → ℝ) : ℝ :=
  (∑ x : V, f x) / (Fintype.card V : ℝ)

theorem sum_sub_finiteMean_eq_zero {V : Type*} [Fintype V] [Nonempty V]
    (f : V → ℝ) :
    (∑ x : V, (f x - finiteMean f)) = 0 := by
  have hcard : (Fintype.card V : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp only [Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, finiteMean]
  field_simp
  ring

theorem sum_sq_sub_finiteMean_le {V : Type*} [Fintype V] [Nonempty V]
    (f : V → ℝ) (c : ℝ) :
    (∑ x : V, (f x - finiteMean f) ^ 2) ≤
      ∑ x : V, (f x - c) ^ 2 := by
  have hpoint (x : V) :
      (f x - c) ^ 2 =
        (f x - finiteMean f) ^ 2 +
          2 * (finiteMean f - c) * (f x - finiteMean f) +
          (finiteMean f - c) ^ 2 := by
    ring
  have hidentity :
      (∑ x : V, (f x - c) ^ 2) =
        (∑ x : V, (f x - finiteMean f) ^ 2) +
          (Fintype.card V : ℝ) * (finiteMean f - c) ^ 2 := by
    calc
      (∑ x : V, (f x - c) ^ 2) =
          ∑ x : V,
            ((f x - finiteMean f) ^ 2 +
              2 * (finiteMean f - c) * (f x - finiteMean f) +
              (finiteMean f - c) ^ 2) :=
            Finset.sum_congr rfl (fun x _ => hpoint x)
      _ = (∑ x : V, (f x - finiteMean f) ^ 2) +
          2 * (finiteMean f - c) *
            (∑ x : V, (f x - finiteMean f)) +
          (Fintype.card V : ℝ) * (finiteMean f - c) ^ 2 := by
            simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
              Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = (∑ x : V, (f x - finiteMean f) ^ 2) +
          (Fintype.card V : ℝ) * (finiteMean f - c) ^ 2 := by
            rw [sum_sub_finiteMean_eq_zero]
            ring
  rw [hidentity]
  exact le_add_of_nonneg_right
    (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))

/-- Internal interface connecting the split non-sofic proof modules. -/
noncomputable def lowerLevel {V : Type*} [Fintype V]
    (f : V → ℝ) (a : ℝ) : Finset V := by
  classical
  exact Finset.univ.filter fun x => f x < a

/-- Internal interface connecting the split non-sofic proof modules. -/
noncomputable def upperLevel {V : Type*} [Fintype V]
    (f : V → ℝ) (a : ℝ) : Finset V := by
  classical
  exact Finset.univ.filter fun x => a < f x

@[simp] public theorem mem_lowerLevel {V : Type*} [Fintype V]
    (f : V → ℝ) (a : ℝ) (x : V) :
    x ∈ lowerLevel f a ↔ f x < a := by
  classical
  simp only [lowerLevel, Finset.mem_filter, Finset.mem_univ, true_and]

@[simp] public theorem mem_upperLevel {V : Type*} [Fintype V]
    (f : V → ℝ) (a : ℝ) (x : V) :
    x ∈ upperLevel f a ↔ a < f x := by
  classical
  simp only [upperLevel, Finset.mem_filter, Finset.mem_univ, true_and]

theorem exists_finite_real_median {V : Type*} [Fintype V] [Nonempty V]
    (f : V → ℝ) :
    ∃ m : ℝ,
      2 * (lowerLevel f m).card ≤ Fintype.card V ∧
      2 * (upperLevel f m).card ≤ Fintype.card V := by
  classical
  let values : Finset ℝ := Finset.univ.image f
  have hvalues : values.Nonempty := by
    obtain ⟨x⟩ := ‹Nonempty V›
    refine ⟨f x, ?_⟩
    exact Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩
  let a : ℝ := values.min' hvalues
  have ha_values : a ∈ values := Finset.min'_mem values hvalues
  have ha_lower : lowerLevel f a = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hx_lt : f x < a := (mem_lowerLevel f a x).mp hx
    have hx_values : f x ∈ values :=
      Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩
    exact (not_lt_of_ge (Finset.min'_le values (f x) hx_values)) hx_lt
  let candidates : Finset ℝ :=
    values.filter fun c => 2 * (lowerLevel f c).card ≤ Fintype.card V
  have hcandidates : candidates.Nonempty := by
    refine ⟨a, ?_⟩
    apply Finset.mem_filter.mpr
    refine ⟨ha_values, ?_⟩
    simp only [ha_lower, Finset.card_empty, mul_zero, zero_le]
  let m : ℝ := candidates.max' hcandidates
  have hm_candidates : m ∈ candidates :=
    Finset.max'_mem candidates hcandidates
  have hm_lower : 2 * (lowerLevel f m).card ≤ Fintype.card V :=
    (Finset.mem_filter.mp hm_candidates).2
  refine ⟨m, hm_lower, ?_⟩
  by_contra hu
  have hu_large : Fintype.card V < 2 * (upperLevel f m).card :=
    Nat.lt_of_not_ge hu
  have hu_nonempty : (upperLevel f m).Nonempty := by
    apply Finset.card_pos.mp
    omega
  let upperValues : Finset ℝ := (upperLevel f m).image f
  have hupperValues : upperValues.Nonempty :=
    Finset.image_nonempty.mpr hu_nonempty
  let b : ℝ := upperValues.min' hupperValues
  have hb_upperValues : b ∈ upperValues :=
    Finset.min'_mem upperValues hupperValues
  obtain ⟨z, hz_upper, hz_b⟩ := Finset.mem_image.mp hb_upperValues
  have hmb : m < b := by
    rw [← hz_b]
    exact (mem_upperLevel f m z).mp hz_upper
  have hdisjoint : Disjoint (lowerLevel f b) (upperLevel f m) := by
    apply Finset.disjoint_left.mpr
    intro x hx_lower hx_upper
    have hx_lt : f x < b := (mem_lowerLevel f b x).mp hx_lower
    have hx_image : f x ∈ upperValues :=
      Finset.mem_image.mpr ⟨x, hx_upper, rfl⟩
    have hb_le : b ≤ f x :=
      Finset.min'_le upperValues (f x) hx_image
    exact (not_lt_of_ge hb_le) hx_lt
  have hcard :
      (lowerLevel f b).card + (upperLevel f m).card ≤ Fintype.card V := by
    calc
      (lowerLevel f b).card + (upperLevel f m).card =
          ((lowerLevel f b) ∪ (upperLevel f m)).card :=
        (Finset.card_union_of_disjoint hdisjoint).symm
      _ ≤ (Finset.univ : Finset V).card :=
        Finset.card_le_card (Finset.subset_univ _)
      _ = Fintype.card V := Finset.card_univ
  have hb_lower : 2 * (lowerLevel f b).card ≤ Fintype.card V := by
    omega
  have hb_values : b ∈ values := by
    rw [← hz_b]
    exact Finset.mem_image.mpr ⟨z, Finset.mem_univ z, rfl⟩
  have hb_candidates : b ∈ candidates :=
    Finset.mem_filter.mpr ⟨hb_values, hb_lower⟩
  have hb_le_m : b ≤ m :=
    Finset.le_max' candidates b hb_candidates
  exact (not_le_of_gt hmb) hb_le_m

theorem positive_max_iff (a : ℝ) : 0 < max a 0 ↔ 0 < a := by
  by_cases ha : 0 < a
  · rw [max_eq_left ha.le]
  · rw [max_eq_right (le_of_not_gt ha)]
    simp only [lt_self_iff_false, ha]

theorem positiveSupport_max_sub {V : Type*} [Fintype V]
    (f : V → ℝ) (m : ℝ) :
    positiveSupport (fun x => max (f x - m) 0) = upperLevel f m := by
  classical
  ext x
  simp only [mem_positiveSupport, mem_upperLevel,
    positive_max_iff, sub_pos]

theorem positiveSupport_max_sub_reverse {V : Type*} [Fintype V]
    (f : V → ℝ) (m : ℝ) :
    positiveSupport (fun x => max (m - f x) 0) = lowerLevel f m := by
  classical
  ext x
  simp only [mem_positiveSupport, mem_lowerLevel,
    positive_max_iff, sub_pos]

/-- Internal interface connecting the split non-sofic proof modules. -/
def finiteVariance {V : Type*} [Fintype V] (f : V → ℝ) : ℝ :=
  (∑ x : V, (f x - finiteMean f) ^ 2) / (Fintype.card V : ℝ)

theorem finiteVariance_nonneg {V : Type*} [Fintype V]
    (f : V → ℝ) : 0 ≤ finiteVariance f := by
  unfold finiteVariance
  exact div_nonneg
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    (Nat.cast_nonneg _)

theorem card_mul_finiteVariance {V : Type*} [Fintype V] [Nonempty V]
    (f : V → ℝ) :
    (Fintype.card V : ℝ) * finiteVariance f =
      ∑ x : V, (f x - finiteMean f) ^ 2 := by
  have hc : (Fintype.card V : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  unfold finiteVariance
  field_simp

end CheegerPoincare
