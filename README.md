# Spectral graph bounds and discrete Cheeger inequalities

Lean 4 / Mathlib formalizations by **Juan Pablo Traverso Gianini**.
Apache-2.0. This extends the five adjacency-spectrum results registered as
[PALOMAR-2026-10-18-000016 v1](https://palomar-registry.org/entry.html?id=PALOMAR-2026-10-18-000016&version=1).

## Discrete Cheeger–Alon–Milman estimates

For a finite simple graph G on n ≥ 2 vertices, let Δ be its maximum degree and set

- h = infimum of |∂A| / |A| over 0 < |A| and 2|A| ≤ n;
- E(f) = one half of the sum of (f(u)−f(v))² over **oriented** adjacent pairs;
- λ = infimum of E(f) / sum(f²), over nonzero real functions with sum(f) = 0.

The edge boundary ∂A counts each crossing undirected edge once. Thus E is the
quadratic form of the **unnormalized combinatorial Laplacian**, D−A. The new result is

**λ / 2 ≤ h, and h² ≤ 2Δλ.**

No connectivity, regularity, positive-degree, or positive-gap hypothesis is imposed.
In particular, disconnected and edgeless graphs are included. The condition n ≥ 2
makes both variational sets nonempty. No assertion about a second eigenvalue on
zero or one vertex is made.

The definition of λ is the standard Rayleigh variational form of the spectral gap.
The package proves that it is exactly the greatest mean-zero Poincaré constant,
identifies E with Mathlib's actual `SimpleGraph.lapMatrix` quadratic form, and
bounds every nonzero Laplacian eigenvalue below by λ. An identity with a sorted
`Matrix.IsHermitian.eigenvalues₀` index is not part of this delivery.

## Selected statements

The five previously registered adjacency-spectrum results remain:

| Namespace `AdjacencySpectrum` | Result |
| --- | --- |
| `average_degree_le` | Average degree ≤ largest adjacency eigenvalue |
| `le_maxDegree` | Largest adjacency eigenvalue ≤ maximum degree |
| `wilf` | Colorability with floor(λ_max)+1 colors |
| `hoffman_chromatic` | Hoffman's chromatic lower bound |
| `hoffman_ratio` | Hoffman's independent-set ratio bound for regular graphs |

Six new contracts are in namespace `GraphCheeger`:

| Theorem | Result |
| --- | --- |
| `cheeger_inequalities` | Both discrete Cheeger inequalities above |
| `poincare` | h² · sum(f²) ≤ 2ΔE(f) for every mean-zero real f |
| `le_gap_iff` | l ≤ λ iff l · sum(f²) ≤ E(f) for every mean-zero f |
| `spectral_cut_bound` | λ|A|(n−|A|) ≤ n|∂A| for every nonempty proper A |
| `energy_eq_laplacian` | E(f) = fᵀ(D−A)f, using Mathlib's Laplacian |
| `gap_le_laplacian_eigenvalue` | Every nonzero Laplacian eigenvalue is at least λ |

The cut estimate is the complementary-set, distance-one case of Alon–Milman's
spectral cut argument. These are finite discrete graph results. The manifold
Cheeger theorem, concentration/diameter results, explicit expander families,
superconcentrators, infinite-graph transience, and the remaining results of the
source papers are outside scope.

## Proof and reuse

The lower spectral estimate uses a finite coarea argument. A nonnegative function
with support on at most half the vertices is reduced by peeling off its smallest
positive level. Expansion bounds the resulting boundary terms. Applying this to
f², followed by Cauchy–Schwarz and the maximum-degree bound, gives a small-support
Poincaré inequality. A finite real median splits an arbitrary function into
positive and negative parts with small supports. The mean minimizes squared
deviation, yielding the mean-zero estimate. Taking the Rayleigh infimum gives
h² ≤ 2Δλ, including the separate zero-degree case.

For the opposite direction, the indicator of a nonempty small set is centered
by its mean. Its energy is exactly its edge boundary and its squared mass is
|A|(n−|A|)/n. The Rayleigh test gives both the cut estimate and λ/2 ≤ h.

The finite median lemmas are extracted from Lean Pool. The support-peeling proof
adapts its permutation coarea argument to graph arcs. See
[THIRD_PARTY.md](THIRD_PARTY.md) for exact source commits, authors, licenses, and
changes. The five original spectral proof bodies are retained, with aggregate
Mathlib imports replaced by specific modules. Their original Aristotle/Claude
provenance is preserved. The new graph estimates were developed with OpenAI Codex.

## Sources

- N. Alon and V. D. Milman, *λ₁, Isoperimetric Inequalities for Graphs, and
  Superconcentrators*, J. Combin. Theory B 38 (1985), 73–88,
  [doi:10.1016/0095-8956(85)90092-9](https://doi.org/10.1016/0095-8956(85)90092-9),
  [primary open PDF](https://web.math.princeton.edu/~nalon/PDFS/Publications2/lambda%20%20isoperimetric%20inequalities%20for%20graphs%20and%20superconcentrators.pdf),
  especially Section 2, (2.1), and Lemma 2.1.
- J. Dodziuk, *Difference Equations, Isoperimetric Inequality and Transience of
  Certain Random Walks*, Trans. Amer. Math. Soc. 284 (1984), 787–794,
  [institutional record](https://academicworks.cuny.edu/gc_pubs/181/),
  doi:10.1090/S0002-9947-1984-0743744-X. Historical background for discrete Cheeger estimates;
  its infinite-graph results are not claimed here.
- The preserved adjacency-spectrum statements concern Collatz–Sinogowitz (1957),
  Wilf (1967), Hoffman (1970), and the regular-graph ratio bound discussed by
  Lovász (1979). Their bibliography and provenance remain in `formalization.yaml`.

## Verification

Lean `v4.35.0-rc3`, Mathlib
`c55e6e786f49471c72fbddbec5415808896aec1e`.

```sh
./scripts/check.sh
```

The package checks strict solution compilation, a boundary/axiom audit,
**eleven theorem types and six explicit definitions** against an independent
Challenge, and both Lean's default kernel and NanoDa. The only permitted axioms
are `propext`, `Classical.choice`, and `Quot.sound`. Challenge contains eleven
intentional theorem placeholders; definitions and proof modules contain none.

The audit checks the single-edge graph, including exact h = 1 and λ = 2, the
oriented/undirected counting factors, and the zero expansion and gap of an
edgeless three-vertex graph. See [VERIFICATION.md](VERIFICATION.md) and
[MATHLIB_DEFINITIONS.md](MATHLIB_DEFINITIONS.md).

GitHub workflows run strict Lean CI and the official full Palomar mechanical
preflight. Consult their published results for remote status. **Preflight is not
registry submission or registration.** No independent human mathematical review
or mathematical novelty is claimed.
