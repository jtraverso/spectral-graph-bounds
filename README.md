# Spectral bounds on the chromatic and independence numbers in Lean 4

Author and maintainer: **Juan Pablo Traverso Gianini**. Licence: Apache-2.0 (see `LICENSE`).

Let `G` be a finite simple graph on a nonempty vertex type, `A` its real adjacency matrix
(Mathlib's `SimpleGraph.adjMatrix`), and `λ_max`, `λ_min` its largest and smallest eigenvalues
(`Matrix.IsHermitian.eigenvalues`). All statements are in the namespace `AdjacencySpectrum`:

1. `average_degree_le` and `le_maxDegree` (**Collatz–Sinogowitz 1957**): the average degree
   `2|E|/n` is at most `λ_max`, and `λ_max` is at most the maximum degree.
2. `wilf`, **Wilf's theorem (1967)**: `G` is `(⌊λ_max⌋ + 1)`-colourable.
3. `hoffman_chromatic`, **Hoffman's bound (1970)**: if `G` has an edge, every proper colouring
   with `c` colours has `1 − λ_max/λ_min ≤ c`.
4. `hoffman_ratio`, **Hoffman's ratio bound**: if `G` is `k`-regular with `k ≥ 1`, every
   independent set has at most `n(−λ_min)/(k − λ_min)` vertices.

The statements take the hypothesis `hA : (G.adjMatrix ℝ).IsHermitian`, which is needed to speak
of the eigenvalues and always holds (the adjacency matrix is symmetric). Mathlib has the spectral
theorem for Hermitian matrices but none of these bounds.

## Files

- [`Challenge.lean`](Challenge.lean): the audited statements. It imports only Mathlib.
- [`Solution.lean`](Solution.lean) and [`SpectralLib/`](SpectralLib): the proofs.
- [`comparator.json`](comparator.json): the theorems that are compared.
- [`MATHLIB_DEFINITIONS.md`](MATHLIB_DEFINITIONS.md): verbatim copies of the Mathlib definitions
  used.
- [`formalization.yaml`](formalization.yaml): provenance, sources and process.

## How the proofs go

* **Rayleigh bounds.** Expanding the quadratic form of `A` in an orthonormal eigenbasis (Mathlib's
  spectral theorem) gives `λ_min ‖x‖² ≤ xᵀAx ≤ λ_max ‖x‖²`.
* **Degrees.** `x = 1` gives `2|E| ≤ n λ_max`. For a unit eigenvector `x` of `λ_max`, the
  eigenvalue equation at a coordinate of largest absolute value gives `λ_max ≤ Δ`.
* **Wilf.** Testing the quadratic form on the indicator vector of a vertex set `S` shows that some
  vertex has at most `λ_max` neighbours in `S`; colouring greedily in the reverse of such a
  removal order uses at most `⌊λ_max⌋ + 1` colours.
* **Hoffman.** The Rayleigh lower bound is applied to vectors combining a `λ_max`-eigenvector (the
  all-ones vector in the regular case) with vectors supported on independent sets: the colour
  classes for the chromatic bound, the given independent set for the ratio bound.

## Sources

* L. Collatz, U. Sinogowitz, *Spektren endlicher Grafen*, Abh. Math. Sem. Univ. Hamburg 21 (1957)
  63–77, doi:10.1007/BF02941924.
* H. S. Wilf, *The eigenvalues of a graph and its chromatic number*, J. London Math. Soc. 42
  (1967) 330–332, doi:10.1112/jlms/s1-42.1.330.
* A. J. Hoffman, *On eigenvalues and colorings of graphs*, in: B. Harris (ed.), Graph Theory and
  its Applications, Academic Press, New York (1970), 79–91.
* L. Lovász, *On the Shannon capacity of a graph*, IEEE Trans. Inform. Theory 25 (1979) 1–7,
  doi:10.1109/TIT.1979.1055985 (Hoffman's ratio bound for regular graphs, obtained there through the
  bound on the theta function).

## Authorship and use of AI

The author chose the results. The statements and proof plan were written with Claude in Claude
Code. Harmonic's Aristotle produced the proofs, which were audited and rebuilt locally. Lean
checks everything mechanically. See `formalization.yaml`.

## Building

Lean `v4.35.0-rc3`, Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`:

```bash
lake exe cache get
lake build
```
