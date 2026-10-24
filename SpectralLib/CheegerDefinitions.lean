/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import SpectralLib.Median

/-! # CheegerDefinitions
Finite graph expansion and variational spectral estimates. -/

@[expose] public section

noncomputable section

namespace GraphCheeger

open Finset

universe u
variable {V : Type u} [Fintype V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Both orientations of each edge. -/
def arcs : Finset (V × V) := univ.filter (fun e => G.Adj e.1 e.2)

open Classical in
/-- The edges crossing from A to its complement, counted once. -/
noncomputable def boundary (A : Finset V) : ℕ :=
  ((arcs G).filter (fun e => e.1 ∈ A ∧ e.2 ∉ A)).card

/-- The unnormalized graph Dirichlet energy; each undirected edge contributes once. -/
def energy (f : V → ℝ) : ℝ :=
  (∑ e ∈ arcs G, (f e.1 - f e.2) ^ 2) / 2

def mass (f : V → ℝ) : ℝ := ∑ x, f x ^ 2

def variation (f : V → ℝ) : ℝ := ∑ e ∈ arcs G, |f e.1 - f e.2|

/-- Edge expansion over nonempty sets of at most half the vertices. -/
noncomputable def cheegerConstant : ℝ :=
  sInf {r : ℝ | ∃ A : Finset V, 0 < A.card ∧ 2 * A.card ≤ Fintype.card V ∧
    r = (boundary G A : ℝ) / A.card}

/-- The spectral gap in Rayleigh variational form on the orthogonal complement of constants. -/
noncomputable def spectralGap : ℝ :=
  sInf {r : ℝ | ∃ f : V → ℝ, (∑ x, f x) = 0 ∧ 0 < mass f ∧
    r = energy G f / mass f}

open Classical in
@[simp] theorem mem_arcs (e : V × V) : e ∈ arcs G ↔ G.Adj e.1 e.2 := by simp [arcs]

open Classical in
theorem sum_arcs (F : V × V → ℝ) :
    ∑ e ∈ arcs G, F e = ∑ x, ∑ y, if G.Adj x y then F (x, y) else 0 := by
  simp [arcs, Finset.sum_filter, Fintype.sum_prod_type]

open Classical in
theorem sum_arcs_swap (F : V × V → ℝ) :
    ∑ e ∈ arcs G, F (e.2, e.1) = ∑ e ∈ arcs G, F e := by
  rw [sum_arcs, sum_arcs, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  simp only [G.adj_comm]

open Classical in
theorem energy_nonneg (f : V → ℝ) : 0 ≤ energy G f := by
  unfold energy
  positivity

open Classical in
theorem energy_sub_const (f : V → ℝ) (m : ℝ) :
    energy G (fun x => f x - m) = energy G f := by
  simp [energy]

open Classical in
theorem mass_nonneg (f : V → ℝ) : 0 ≤ mass f := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

end GraphCheeger
