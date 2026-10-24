/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import SpectralLib.CheegerPoincare

/-! # CheegerVariational
Finite graph expansion and variational spectral estimates. -/

@[expose] public section

noncomputable section

namespace GraphCheeger

open Finset

universe u
variable {V : Type u} [Fintype V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def cutValues : Set ℝ := {r | ∃ A : Finset V, 0 < A.card ∧
  2 * A.card ≤ Fintype.card V ∧ r = (boundary G A : ℝ) / A.card}
def rayleighValues : Set ℝ := {r | ∃ f : V → ℝ, (∑ x, f x) = 0 ∧
  0 < mass f ∧ r = energy G f / mass f}

open Classical in
theorem cuts_bddBelow : BddBelow (cutValues G) := by
  refine ⟨0, ?_⟩
  rintro r ⟨A, _, _, rfl⟩
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

open Classical in
theorem rays_bddBelow : BddBelow (rayleighValues G) := by
  refine ⟨0, ?_⟩
  rintro r ⟨f, _, hf, rfl⟩
  exact div_nonneg (energy_nonneg G f) hf.le

open Classical in
theorem cuts_nonempty (hn : 2 ≤ Fintype.card V) : (cutValues G).Nonempty := by
  have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨v⟩ := ‹Nonempty V›
  exact ⟨(boundary G {v} : ℝ) / ({v} : Finset V).card, {v}, by simp, by simpa using hn, rfl⟩

open Classical in
theorem cheeger_nonneg (hn : 2 ≤ Fintype.card V) : 0 ≤ cheegerConstant G := by
  apply le_csInf (cuts_nonempty G hn)
  rintro r ⟨A, _, _, rfl⟩
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

open Classical in
theorem expansion_bound (A : Finset V) (hhalf : 2 * A.card ≤ Fintype.card V) :
    cheegerConstant G * A.card ≤ boundary G A := by
  by_cases hz : A.card = 0
  · simp [hz]
  have hp : (0 : ℝ) < A.card := by exact_mod_cast (Nat.pos_of_ne_zero hz)
  have h := csInf_le (cuts_bddBelow G)
    (show (boundary G A : ℝ) / A.card ∈ cutValues G from ⟨A, Nat.pos_of_ne_zero hz, hhalf, rfl⟩)
  exact (le_div_iff₀ hp).mp h

open Classical in
noncomputable def indicator (A : Finset V) : V → ℝ := fun x => if x ∈ A then 1 else 0

open Classical in
noncomputable def centeredIndicator (A : Finset V) : V → ℝ :=
  fun x => indicator A x - (A.card : ℝ) / Fintype.card V

open Classical in
theorem energy_indicator (A : Finset V) : energy G (indicator A) = boundary G A := by
  classical
  have hpoint (e : V × V) : (indicator A e.1 - indicator A e.2) ^ 2 =
      (if e.1 ∈ A ∧ e.2 ∉ A then (1 : ℝ) else 0) +
      (if e.1 ∉ A ∧ e.2 ∈ A then (1 : ℝ) else 0) := by
    by_cases hx : e.1 ∈ A <;> by_cases hy : e.2 ∈ A <;> simp [indicator, hx, hy]
  unfold energy
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, sum_crossing, sum_entering]
  ring

open Classical in
theorem centered_sum [Nonempty V] (A : Finset V) : (∑ x, centeredIndicator A x) = 0 := by
  classical
  have hn : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [centeredIndicator, indicator, Finset.sum_sub_distrib, hn, mul_div_cancel₀]

open Classical in
theorem centered_mass [Nonempty V] (A : Finset V) :
    mass (centeredIndicator A) = (A.card : ℝ) * (Fintype.card V - A.card) / Fintype.card V := by
  classical
  have hn : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  let a : ℝ := A.card
  let n : ℝ := Fintype.card V
  let c : ℝ := a / n
  have hpoint (x : V) : (indicator A x - c) ^ 2 = indicator A x - 2 * c * indicator A x + c ^ 2 := by
    by_cases hx : x ∈ A <;> simp only [indicator, hx, ↓reduceIte] <;> ring
  change (∑ x, (indicator A x - c) ^ 2) = _
  simp_rw [hpoint]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hi : (∑ x, indicator A x) = a := by simp [indicator, a]
  rw [hi]
  dsimp [c, a, n]
  field_simp
  ring

open Classical in
theorem centered_mass_pos [Nonempty V] (A : Finset V)
    (hpos : 0 < A.card) (hproper : A.card < Fintype.card V) :
    0 < mass (centeredIndicator A) := by
  rw [centered_mass]
  have ha : (0 : ℝ) < A.card := by exact_mod_cast hpos
  have hn : (A.card : ℝ) < Fintype.card V := by exact_mod_cast hproper
  positivity

open Classical in
theorem rays_nonempty (hn : 2 ≤ Fintype.card V) : (rayleighValues G).Nonempty := by
  have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨v⟩ := ‹Nonempty V›
  let f := centeredIndicator ({v} : Finset V)
  exact ⟨energy G f / mass f, f, centered_sum _,
    centered_mass_pos _ (by simp) (by simpa using (show 1 < Fintype.card V by omega)), rfl⟩

open Classical in
theorem gap_nonneg (hn : 2 ≤ Fintype.card V) : 0 ≤ spectralGap G := by
  apply le_csInf (rays_nonempty G hn)
  rintro r ⟨f, _, hf, rfl⟩
  exact div_nonneg (energy_nonneg G f) hf.le

open Classical in
theorem gap_le_rayleigh (f : V → ℝ) (hzero : (∑ x, f x) = 0) (hf : 0 < mass f) :
    spectralGap G ≤ energy G f / mass f :=
  csInf_le (rays_bddBelow G) ⟨f, hzero, hf, rfl⟩

open Classical in
theorem gap_le_cut_ratio (hn : 2 ≤ Fintype.card V) (A : Finset V)
    (hpos : 0 < A.card) (hhalf : 2 * A.card ≤ Fintype.card V) :
    spectralGap G ≤ 2 * ((boundary G A : ℝ) / A.card) := by
  have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have hproper : A.card < Fintype.card V := by omega
  have hp := centered_mass_pos A hpos hproper
  have hgap := gap_le_rayleigh G (centeredIndicator A) (centered_sum A) hp
  have he : energy G (centeredIndicator A) = boundary G A := by
    change energy G (fun x => indicator A x - (A.card : ℝ) / Fintype.card V) = _
    rw [energy_sub_const, energy_indicator]
  have ha : (0 : ℝ) < A.card := by exact_mod_cast hpos
  have hnpos : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hhalfR : (2 : ℝ) * A.card ≤ Fintype.card V := by exact_mod_cast hhalf
  have hmass : (A.card : ℝ) / 2 ≤ mass (centeredIndicator A) := by
    rw [centered_mass, le_div_iff₀ hnpos]
    nlinarith
  calc
    _ ≤ (boundary G A : ℝ) / mass (centeredIndicator A) := by simpa only [he] using hgap
    _ ≤ (boundary G A : ℝ) / ((A.card : ℝ) / 2) :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) hmass
    _ = _ := by ring

open Classical in
theorem spectral_upper (hn : 2 ≤ Fintype.card V) : spectralGap G / 2 ≤ cheegerConstant G := by
  apply le_csInf (cuts_nonempty G hn)
  rintro r ⟨A, hpos, hhalf, rfl⟩
  have h := gap_le_cut_ratio G hn A hpos hhalf
  linarith

open Classical in
theorem boundary_singleton (v : V) : boundary G {v} = G.degree v := by
  have heq : (arcs G).filter (fun e => e.1 ∈ ({v} : Finset V) ∧ e.2 ∉ ({v} : Finset V)) =
      ({v} : Finset V) ×ˢ G.neighborFinset v := by
    ext e
    rcases e with ⟨x, y⟩
    simp only [Finset.mem_filter, mem_arcs, Finset.mem_singleton, Finset.mem_product,
      SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨hxy, rfl, _⟩
      exact ⟨rfl, hxy⟩
    · rintro ⟨rfl, hvy⟩
      exact ⟨hvy, rfl, hvy.ne.symm⟩
  rw [boundary, heq, Finset.card_product, Finset.card_singleton, one_mul,
    SimpleGraph.card_neighborFinset_eq_degree]

open Classical in
theorem cheeger_le_maxDegree (hn : 2 ≤ Fintype.card V) : cheegerConstant G ≤ G.maxDegree := by
  have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨v⟩ := ‹Nonempty V›
  have h := expansion_bound G {v} (by simpa using hn)
  rw [boundary_singleton] at h
  simp only [Finset.card_singleton, Nat.cast_one, mul_one] at h
  exact h.trans (by exact_mod_cast G.degree_le_maxDegree v)

open Classical in
theorem spectral_lower (hn : 2 ≤ Fintype.card V) :
    cheegerConstant G ^ 2 ≤ 2 * G.maxDegree * spectralGap G := by
  have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  by_cases hz : G.maxDegree = 0
  · have hzero : cheegerConstant G = 0 := by
      have h := cheeger_le_maxDegree G hn
      rw [hz, Nat.cast_zero] at h
      exact le_antisymm h (cheeger_nonneg G hn)
    simp [hz, hzero]
  have hd : (0 : ℝ) < 2 * G.maxDegree := by
    have : (0 : ℝ) < G.maxDegree := by exact_mod_cast Nat.pos_of_ne_zero hz
    positivity
  have hbound : cheegerConstant G ^ 2 / (2 * G.maxDegree) ≤ spectralGap G := by
    apply le_csInf (rays_nonempty G hn)
    rintro r ⟨f, hzero, hf, rfl⟩
    have h := poincare_of_expansion G (cheegerConstant G) (cheeger_nonneg G hn)
      (expansion_bound G) f hzero
    rw [div_le_div_iff₀ hd hf]
    nlinarith only [h]
  simpa only [mul_comm] using (div_le_iff₀ hd).mp hbound

open Classical in
/-- Discrete Cheeger inequalities, including disconnected and edgeless graphs. -/
theorem cheeger_inequalities (hn : 2 ≤ Fintype.card V) :
    spectralGap G / 2 ≤ cheegerConstant G ∧
      cheegerConstant G ^ 2 ≤ 2 * G.maxDegree * spectralGap G :=
  ⟨spectral_upper G hn, spectral_lower G hn⟩

open Classical in
/-- Universal mean-zero Poincaré estimate with the graph's actual expansion constant. -/
theorem poincare (hn : 2 ≤ Fintype.card V)
    (f : V → ℝ) (hzero : (∑ x, f x) = 0) :
    cheegerConstant G ^ 2 * mass f ≤ 2 * G.maxDegree * energy G f := by
  have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  exact poincare_of_expansion G (cheegerConstant G) (cheeger_nonneg G hn) (expansion_bound G) f hzero

open Classical in
/-- The variational gap is exactly the greatest mean-zero Poincaré constant. -/
theorem le_gap_iff (hn : 2 ≤ Fintype.card V) (l : ℝ) :
    l ≤ spectralGap G ↔ ∀ f : V → ℝ, (∑ x, f x) = 0 → l * mass f ≤ energy G f := by
  constructor
  · intro hl f hzero
    by_cases hz : mass f = 0
    · rw [hz, mul_zero]
      exact energy_nonneg G f
    · have hp : 0 < mass f := lt_of_le_of_ne (mass_nonneg f) (Ne.symm hz)
      exact (le_div_iff₀ hp).mp (hl.trans (gap_le_rayleigh G f hzero hp))
  · intro hp
    apply le_csInf (rays_nonempty G hn)
    rintro r ⟨f, hzero, hf, rfl⟩
    exact (le_div_iff₀ hf).mpr (hp f hzero)

open Classical in
/-- The complementary-set case of the Alon–Milman spectral cut estimate. -/
theorem spectral_cut_bound (A : Finset V) (hpos : 0 < A.card)
    (hproper : A.card < Fintype.card V) :
    spectralGap G * A.card * (Fintype.card V - A.card) ≤
      Fintype.card V * (boundary G A : ℝ) := by
  have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hp := centered_mass_pos A hpos hproper
  have h := (le_div_iff₀ hp).mp
    (gap_le_rayleigh G (centeredIndicator A) (centered_sum A) hp)
  have he : energy G (centeredIndicator A) = boundary G A := by
    change energy G (fun x => indicator A x - (A.card : ℝ) / Fintype.card V) = _
    rw [energy_sub_const, energy_indicator]
  rw [he, centered_mass] at h
  have hm := mul_le_mul_of_nonneg_left h hn.le
  calc
    _ = (Fintype.card V : ℝ) *
        (spectralGap G * ((A.card : ℝ) * (Fintype.card V - A.card) / Fintype.card V)) := by
      field_simp
    _ ≤ _ := hm

end GraphCheeger
