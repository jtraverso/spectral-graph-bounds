# Reused Lean code and provenance

## Existing spectral formalizations

The five adjacency-spectrum statements and their proofs originate in the registered
`jtraverso/spectral-graph-bounds` commit
`8d8b4ce17e56165b5f1ad3b285fb141666804e1c`,
Palomar entry PALOMAR-2026-10-18-000016 v1. Author and maintainer:
Juan Pablo Traverso Gianini. The original package credits Claude for statements
and proof planning and Harmonic Aristotle for proof production. This provenance
is retained in formalization.yaml. Their proof bodies are preserved; aggregate
Mathlib imports are replaced by the specific required modules. A local unused-section-variable linter exception for Wilf retains its registered nonempty-vertex parameter even though its proof also works without that parameter; theorem type and proof body are unchanged.

## Lean Pool finite median lemmas

Source:
[LeanPool/NonSoficGroup/Foundations.lean](https://github.com/LeanPool/lean-pool/blob/edbe5bd56f476cc2965564676b66199f281ab714/LeanPool/NonSoficGroup/Foundations.lean),
namespace `SoficGroups.CheegerPoincare`.
Commit: `edbe5bd56f476cc2965564676b66199f281ab714`.
Copyright (c) 2026 OpenAI and Dean Cureton.
Authors: OpenAI, Dean Cureton. License: Apache-2.0.

`SpectralLib/Median.lean` extracts positive supports, finite means/variances,
least-squares minimization by the mean, existence of a finite real median, and
the positive-support identities. It removes surrounding group-theoretic
dependencies, moves the namespace to the root, makes the elementary sum lemma
public, and supplies narrow imports and a noncomputable section.
The original copyright and author attribution are retained.

## Adapted finite coarea argument

Source:
[LeanPool/NonSoficGroup/Compression.lean](https://github.com/LeanPool/lean-pool/blob/edbe5bd56f476cc2965564676b66199f281ab714/LeanPool/NonSoficGroup/Compression.lean),
namespace `SoficGroups.KunAdditiveMedianPoincare`, at the same commit, authors
and license.

The support-peeling induction and variation identity in
`SpectralLib/CheegerCoarea.lean` adapt the additive permutation coarea argument
to graph arcs, remove the additive error and bounded-range hypotheses, and use
graph symmetry in place of permutation crossing counts. This is a substantive
adaptation; no group construction or non-soficity theorem is imported or claimed.

The remaining Cheeger, quadratic-energy, Rayleigh-infimum, cut, and Laplacian
proofs were constructed for this extension with OpenAI Codex using Mathlib.
No sub-agents or external proving service were used for this extension.
