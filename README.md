# Jaeger's 4-flow theorem in Lean 4

Author and maintainer: **Juan Pablo Traverso Gianini**. Licence: Apache-2.0 (see `LICENSE`).

A *nowhere-zero integer `k`-flow* on a finite simple graph `G` is a function `φ` on the darts
(oriented edges) of `G` with `φ(d.symm) = −φ(d)`, `0 < |φ(d)| < k` for every dart, and
conservation `∑_{d.fst = v} φ(d) = 0` at every vertex (`JaegerFlow.IsNowhereZeroFlow`). All
statements are in the namespace `JaegerFlow`:

1. `exists_even_cover_of_trees`. If `G` contains two edge-disjoint spanning trees, its edges are
   covered by two subgraphs `H₁, H₂ ≤ G` in which every vertex has even degree; equivalently, `G`
   has a nowhere-zero `ℤ₂ × ℤ₂`-flow.
2. `exists_flow_of_trees`. If `G` contains two edge-disjoint spanning trees, it has a nowhere-zero
   integer 4-flow.
3. `jaeger_four_flow`, **Jaeger's 4-flow theorem (1979)**. Every finite 4-edge-connected graph has
   a nowhere-zero integer 4-flow.

4-edge-connectivity is Mathlib's `SimpleGraph.IsEdgeConnected 4`. Mathlib has no flows; Jaeger's
8-flow theorem for bridgeless graphs is not part of this entry.

## Files

- [`Challenge.lean`](Challenge.lean): the definition of nowhere-zero flows and the audited
  statements. It imports only Mathlib.
- [`Solution.lean`](Solution.lean) and [`JaegerLib/`](JaegerLib): the proofs.
- [`TreePackingLib/`](TreePackingLib): the Nash-Williams–Tutte tree packing theorem, reused
  unchanged from the registered entry
  [PALOMAR-2026-10-17-000008](https://palomar-registry.org/entry.html?id=PALOMAR-2026-10-17-000008&version=1)
  ([jtraverso/nash-williams-trees](https://github.com/jtraverso/nash-williams-trees) @ 101e488).
- [`Euler/`](Euler): Eulerian trails and balanced (Eulerian) orientations, reused unchanged from
  the registered entry
  [PALOMAR-2026-10-16-000016](https://palomar-registry.org/entry.html?id=PALOMAR-2026-10-16-000016&version=1)
  ([jtraverso/euler-petersen](https://github.com/jtraverso/euler-petersen) @ 02c3f1a).
- [`comparator.json`](comparator.json): the theorems that are compared (the comparator also checks
  every definition their statements use, including `IsNowhereZeroFlow`).
- [`MATHLIB_DEFINITIONS.md`](MATHLIB_DEFINITIONS.md): verbatim copies of the Mathlib definitions
  used.
- [`formalization.yaml`](formalization.yaml): provenance, sources and process.

## How the proofs go

* **T-joins.** In a connected graph `T`, every vertex set `W` of even size is the set of
  odd-degree vertices of some subgraph `J ≤ T` (by induction on `#W/2`, taking symmetric
  differences with paths between two vertices of `W`).
* **Even cover.** For `i = 1, 2`, let `J_i ≤ T_i` be the T-join of the odd-degree vertices of
  `G \ T_i` and put `H_i = (G \ T_i) Δ J_i`. Every degree in `H_i` is even, and `H₁ ⊔ H₂ = G`
  because the trees are edge-disjoint.
* **Integer flow.** A balanced orientation of the even graph `H_i` (from `Euler/`) gives a
  conserved antisymmetric `ψ_i` with values in `{−1, 0, 1}`, nonzero exactly on `H_i`. Then
  `φ = ψ₁ + 2ψ₂` takes values in `{±1, ±2, ±3}` on every dart.
* **Jaeger.** A 4-edge-connected graph has two edge-disjoint spanning trees by the Nash-Williams–
  Tutte theorem (`TreePackingLib/`).

## Sources

* F. Jaeger, *Flows and generalized coloring theorems in graphs*, J. Combin. Theory Ser. B 26
  (1979) 205–216, doi:10.1016/0095-8956(79)90057-1.

## Authorship and use of AI

The author chose the result. The statements and proof plan were written with Claude in Claude
Code (the statement was checked by brute force on all 4-edge-connected graphs with 5 to 7
vertices). Harmonic's Aristotle produced the proofs, which were audited and rebuilt locally. Lean
checks everything mechanically. See `formalization.yaml`.

## Building

Lean `v4.35.0-rc3`, Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`:

```bash
lake exe cache get
lake build
```
