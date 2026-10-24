# Verification record

Toolchain: Lean v4.35.0-rc3; Mathlib
`c55e6e786f49471c72fbddbec5415808896aec1e`.

Run `scripts/check.sh`:

- Strict `lake build --wfail` for Solution.
- Strict `lake build Audit --wfail` for the eleven-result axiom and boundary audit.
- `lake build Challenge` for independent contracts; eleven intentional theorem warnings.
- `lake comparator --config comparator.json` for eleven theorem types, six full
  definition bodies, and verification by Lean and NanoDa.

No proof imports Challenge. The permitted axioms are exactly `propext`,
`Classical.choice`, and `Quot.sound`. There are no custom axioms or solution
placeholders. Finite audit calculations use kernel-reduced `decide` and proof
tactics, not `native_decide`.

Compared definitions: `GraphCheeger.arcs`, `boundary`, `energy`, `mass`,
`cheegerConstant`, and `spectralGap`. The independent Challenge repeats their
complete definitions and imports only Mathlib. The expansion and Rayleigh sets
are proved nonempty and bounded below under n ≥ 2; empty-set infimum conventions
are not used to obtain the main estimates.

The energy normalization counts each undirected edge once. For K2, the audit
checks one crossing edge, two oriented arcs, E(f) = 2 sum(f²) on mean-zero
functions, h = 1, λ = 2, and equality λ/2 = h. For the edgeless graph on three
vertices, it verifies h = λ = 0. Connectivity and positive degree are not
required by the main theorem.

The five old spectral proof bodies and contracts are retained. Their imports
are narrowed to the modules actually needed. Source attribution for extracted
and adapted Lean Pool code appears in THIRD_PARTY.md. The variational formulation
is explicit; no equality with a sorted eigenvalue index is asserted.

Successful local logs are stored in `verification/local-checks.log`. The remote
preflight uses the official pipeline pinned at
`c02bbeaed888df45c4e28c4e99dba540ad21552a`, profile `palomar-standard-v1`,
request `cheegerproof`. Published run results establish remote verification status.
Preflight does not submit or register an entry.
