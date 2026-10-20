# Jaeger's 4-flow and 8-flow theorems and Seymour's 6-flow theorem in Lean 4

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

4-edge-connectivity is Mathlib's `SimpleGraph.IsEdgeConnected 4`. Mathlib has no flows.

**Version 2** adds Jaeger's 8-flow theorem, in the namespace `EightFlowTheorem`, for finite graphs
with no bridge (every edge `e` satisfies `¬ G.IsBridge e`, Mathlib's `SimpleGraph.IsBridge`):

4. `exists_even_cover_three`. The edges of a bridgeless graph are covered by three subgraphs in
   which every vertex has even degree (a nowhere-zero `(ℤ₂)³`-flow).
5. `jaeger_eight_flow`, **Jaeger's 8-flow theorem (Jaeger 1979; Kilpatrick 1975)**. Every finite
   bridgeless graph has a nowhere-zero integer 8-flow.
6. `not_isBridge_of_flow`. Conversely, a graph with a nowhere-zero `k`-flow has no bridge.

**Version 3** adds, in the namespace `SixFlowTheorem`, group flows (`SixFlow.IsNowhereZeroGroupFlow`:
antisymmetric, nowhere-zero, conserved functions on darts with values in an abelian group, stated
in `Challenge.lean` verbatim with the same name as in the library):

7. `integer_flow_of_zmod`, **Tutte's theorem (1949, 1954)**. For `k > 0`, a nowhere-zero
   `ℤ/k`-flow lifts to a nowhere-zero integer `k`-flow.
8. `zmod_flow_of_integer`. Conversely, a nowhere-zero integer `k`-flow reduces to a nowhere-zero
   `ℤ/k`-flow.
9. `seymour_six_flow`, **Seymour's 6-flow theorem (1981)**. Every finite bridgeless graph has a
   nowhere-zero integer 6-flow.

## Files

- [`Challenge.lean`](Challenge.lean): the definition of nowhere-zero flows and the audited
  statements. It imports only Mathlib.
- [`Solution.lean`](Solution.lean), [`JaegerLib/`](JaegerLib), (version 2)
  [`EightFlowLib/`](EightFlowLib) and (version 3) [`SixFlowLib/`](SixFlowLib): the proofs.
- [`TreePackingLib/`](TreePackingLib): the Nash-Williams–Tutte tree packing theorem, reused
  unchanged from the registered entry
  [PALOMAR-2026-10-17-000008](https://palomar-registry.org/entry.html?id=PALOMAR-2026-10-17-000008&version=1)
  ([jtraverso/nash-williams-trees](https://github.com/jtraverso/nash-williams-trees) @ 101e488).
- [`Euler/`](Euler): Eulerian trails and balanced (Eulerian) orientations, reused unchanged from
  the registered entry
  [PALOMAR-2026-10-16-000016](https://palomar-registry.org/entry.html?id=PALOMAR-2026-10-16-000016&version=1)
  ([jtraverso/euler-petersen](https://github.com/jtraverso/euler-petersen) @ 02c3f1a).
- [`comparator.json`](comparator.json): the theorems that are compared. It selects only the
  theorems; the definitions `IsNowhereZeroFlow` and `IsNowhereZeroGroupFlow` are not selected
  separately and enter the check only as part of the theorem statements that use them.
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
* **8-flows** (version 2, `EightFlowLib/`).
  - *Bridges.* Summing conservation over the side of a bridge leaves only the value on the
    bridge, which is therefore zero.
  - *Reduction.* By induction on the number of edges, for nowhere-zero `(ℤ₂)³`-flows, staying
    inside simple graphs: even graphs are trivial; a cut whose crossing edges share an endpoint
    splits the graph into two bridgeless pieces; in a 2-edge cut an edge `ab` without common
    neighbours is contracted (the graph stays simple and bridgeless, and the flow lifts back); a
    degree-2 vertex on a triangle is handled with a triangle flow. When none of these applies, the
    graph is 3-edge-connected.
  - *3-edge-connected base case.* An auxiliary graph on `V × Fin 7` (each vertex a 7-clique, each
    edge doubled) is 6-edge-connected, so the Nash-Williams–Tutte theorem gives three
    edge-disjoint spanning trees; projected to `G` they are connected spanning subgraphs with no
    edge common to all three, and their cotrees extend to three even subgraphs covering `G` (as in
    version 1).
  - *Integer flow.* Balanced orientations of the three even subgraphs give `ψ₁, ψ₂, ψ₃` with
    values in `{−1, 0, 1}`, and `φ = ψ₁ + 2ψ₂ + 4ψ₃` takes values in `{±1, …, ±7}`.
* **Tutte's theorem** (version 3, `SixFlowLib/SixFlowTutte.lean`). Among the antisymmetric integer
  lifts of a `ℤ/k`-flow with values in `(−k, k)`, take one minimising the total vertex excess (each
  excess is a multiple of `k`). If some vertex has positive excess, either it reaches a vertex of
  negative excess along darts with positive value, and shifting by `k` along that path lowers the
  total excess, or summing the excesses over the reachable set gives a contradiction.
* **Seymour's 6-flow theorem** (version 3, `SixFlowLib/`). The proof works with an internal
  multigraph model (`SixFlowMG.lean`). An ear argument puts any two vertices of a bridgeless piece
  on a common connected even subgraph (`SixFlowClaimB.lean`). Seymour's greedy step
  (`SixFlowGreedy.lean`) grows a vertex set `U` and an even edge set `F` inside it such that every
  `ℤ/3`-demand on `U` is met by a function nonzero off `F`, attaching a minimal leaf piece through
  two edges; when every cut has at least three edges this gives a nowhere-zero `ℤ/2 × ℤ/3`-flow.
  An induction on the number of edges splits empty cuts and contracts one edge of each 2-edge cut
  (`SixFlowReduce.lean`). The flow is converted to darts, to `ℤ/6` by the Chinese remainder
  theorem, and to an integer 6-flow by Tutte's theorem (`SixFlowConvert.lean`).

## Sources

* F. Jaeger, *Flows and generalized coloring theorems in graphs*, J. Combin. Theory Ser. B 26
  (1979) 205–216, doi:10.1016/0095-8956(79)90057-1.
* P. A. Kilpatrick, *Tutte's first colour-cycle conjecture*, Ph.D. thesis, University of Cape
  Town (1975).
* P. D. Seymour, *Nowhere-zero 6-flows*, J. Combin. Theory Ser. B 30 (1981) 130–135,
  doi:10.1016/0095-8956(81)90058-7.
* W. T. Tutte, *A contribution to the theory of chromatic polynomials*, Canad. J. Math. 6 (1954)
  80–91, doi:10.4153/CJM-1954-010-9.

## Authorship and use of AI

The author chose the result. The statements and proof plan were written with Claude in Claude
Code (the statement was checked by brute force on all 4-edge-connected graphs with 5 to 7
vertices). Harmonic's Aristotle produced the proofs (one run for each version), which were audited
and rebuilt locally. Lean
checks everything mechanically. See `formalization.yaml`.

## Building

Lean `v4.35.0-rc3`, Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`:

```bash
lake exe cache get
lake build
```
