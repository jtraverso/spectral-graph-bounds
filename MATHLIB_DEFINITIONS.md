# Mathlib definitions used by the spectral bound statements

Verbatim excerpts of the Mathlib definitions used by the statements in `Challenge.lean`, at the
pinned Mathlib revision `c55e6e786f49471c72fbddbec5415808896aec1e` (tag `v4.35.0-rc3`, repository
https://github.com/leanprover-community/mathlib4). Mathlib is released under the Apache-2.0
licence. Each excerpt gives the file and line at that revision; the complete source is at
`https://github.com/leanprover-community/mathlib4/blob/c55e6e786f49471c72fbddbec5415808896aec1e/<file>`.

These excerpts are provided so that the meaning of every imported notion used by the
Challenge can be audited without fetching Mathlib.

## SimpleGraph

`Mathlib/Combinatorics/SimpleGraph/Basic.lean`, line 95:

```lean
/-- A simple graph is an irreflexive symmetric relation `Adj` on a vertex type `V`.
The relation describes which pairs of vertices are adjacent.
There is exactly one edge for every pair of adjacent vertices;
see `SimpleGraph.edgeSet` for the corresponding edge set.
-/
@[ext, aesop safe constructors (rule_sets := [SimpleGraph]), wikidata Q141488]
structure SimpleGraph (V : Type u) where
  /-- The adjacency relation of a simple graph. -/
  Adj : V → V → Prop
  symm : Std.Symm Adj := by aesop_graph
  loopless : Std.Irrefl Adj := by aesop_graph
```

## SimpleGraph.edgeFinset

`Mathlib/Combinatorics/SimpleGraph/Finite.lean`, line 59:

```lean
/-- The `edgeSet` of the graph as a `Finset`. -/
def edgeFinset : Finset (Sym2 V) :=
  Set.toFinset G.edgeSet
```

## SimpleGraph.neighborFinset

`Mathlib/Combinatorics/SimpleGraph/Finite.lean`, line 169:

```lean
/-- `G.neighborFinset v` is the `Finset` version of `G.neighborSet v` in case `G` is
locally finite at `v`. -/
def neighborFinset : Finset V :=
  (G.neighborSet v).toFinset
```

## SimpleGraph.degree

`Mathlib/Combinatorics/SimpleGraph/Finite.lean`, line 242:

```lean
/-- `G.degree v` is the number of vertices adjacent to `v`. -/
def degree : ℕ := #(G.neighborFinset v)
```

## SimpleGraph.IsRegularOfDegree

`Mathlib/Combinatorics/SimpleGraph/Finite.lean`, line 390:

```lean
/-- A locally finite simple graph is regular of degree `d` if every vertex has degree `d`. -/
@[wikidata Q826467]
def IsRegularOfDegree (d : ℕ) : Prop :=
  ∀ v : V, G.degree v = d
```

## SimpleGraph.maxDegree

`Mathlib/Combinatorics/SimpleGraph/Finite.lean`, line 496:

```lean
/-- The maximum degree of all vertices (and `0` if there are no vertices).
The key properties of this are given in `exists_maximal_degree_vertex`, `degree_le_maxDegree`
and `maxDegree_le_of_forall_degree_le`. -/
def maxDegree [DecidableRel G.Adj] : ℕ :=
  WithBot.unbotD 0 (univ.image fun v => G.degree v).max
```

## SimpleGraph.adjMatrix

`Mathlib/Combinatorics/SimpleGraph/AdjMatrix.lean`, line 238:

```lean
/-- `adjMatrix G α` is the matrix `A` such that `A i j = (1 : α)` if `i` and `j` are
  adjacent in the simple graph `G`, and otherwise `A i j = 0`. -/
def adjMatrix [Zero α] [One α] : Matrix V V α :=
  of fun i j => if G.Adj i j then (1 : α) else 0
```

## Matrix.IsHermitian

`Mathlib/LinearAlgebra/Matrix/Hermitian.lean`, line 44:

```lean
/-- A matrix is Hermitian if it is equal to its conjugate transpose. On the reals, this definition
captures symmetric matrices. -/
def IsHermitian (A : Matrix n n α) : Prop := Aᴴ = A
```

## Matrix.IsHermitian.eigenvalues₀

`Mathlib/Analysis/Matrix/Spectrum.lean`, line 60:

```lean
/-- The eigenvalues of a Hermitian matrix, indexed by `Fin (Fintype.card n)` where `n` is the index
type of the matrix. -/
noncomputable def eigenvalues₀ : Fin (Fintype.card n) → ℝ :=
  (isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalues finrank_euclideanSpace
```

## Matrix.IsHermitian.eigenvalues

`Mathlib/Analysis/Matrix/Spectrum.lean`, line 67:

```lean
/-- The eigenvalues of a Hermitian matrix, reusing the index `n` of the matrix entries. -/
noncomputable def eigenvalues : n → ℝ := fun i =>
  hA.eigenvalues₀ <| (Fintype.equivOfCardEq (Fintype.card_fin _)).symm i
```

## SimpleGraph.Coloring

`Mathlib/Combinatorics/SimpleGraph/Coloring/Vertex.lean`, line 74:

```lean
/-- An `α`-coloring of a simple graph `G` is a homomorphism of `G` into the complete graph on `α`.
This is also known as a proper coloring.
-/
abbrev Coloring (α : Type v) := G →g completeGraph α
```

## SimpleGraph.Colorable

`Mathlib/Combinatorics/SimpleGraph/Coloring/Vertex.lean`, line 163:

```lean
/-- Whether a graph can be colored by at most `n` colors. -/
def Colorable (n : ℕ) : Prop := Nonempty (G.Coloring (Fin n))
```

## SimpleGraph.IsIndepSet

`Mathlib/Combinatorics/SimpleGraph/Clique.lean`, line 907:

```lean
/-- An independent set in a graph is a set of vertices that are pairwise not adjacent. -/
@[wikidata Q1060343]
abbrev IsIndepSet (s : Set α) : Prop :=
  s.Pairwise (fun v w ↦ ¬G.Adj v w)
```
