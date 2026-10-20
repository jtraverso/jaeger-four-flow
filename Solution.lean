/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import JaegerLib.Jaeger
public import EightFlowLib.EightFlow
public import SixFlowLib.SixFlow

/-!
# Proofs of the statements in `Challenge.lean`

The theorems are proved in `JaegerLib/` (namespace `Jaeger`), reusing two registered libraries
unchanged: `TreePackingLib/` (Nash-Williams–Tutte tree packing, PALOMAR-2026-10-17-000008) for
the two edge-disjoint spanning trees of a 4-edge-connected graph, and `Euler/` (Eulerian
orientations, PALOMAR-2026-10-16-000016) for balanced orientations of even subgraphs. In a tree
every vertex set of even size is the odd-degree set of a subgraph (a T-join); taking
`H_i = (G \ T_i) Δ J_i` gives the even cover, and `φ = ψ₁ + 2ψ₂` from balanced orientations of
`H₁, H₂` is the 4-flow. The definition `IsNowhereZeroFlow` below is the same as
`Jaeger.IsNowhereZeroFlow` in the library.

Jaeger's 8-flow theorem (version 2) is proved in `EightFlowLib/` (namespace `EightFlow`), on
top of `JaegerLib/`, `TreePackingLib/` and `Euler/`: an induction on nowhere-zero `(ℤ₂)³`-flows
that splits and contracts 2-edge cuts inside simple graphs, and a 3-edge-connected base case
that applies the Nash-Williams–Tutte theorem to an auxiliary 6-edge-connected graph (each
vertex replaced by a 7-clique, each edge doubled) to get three spanning trees with no common
edge; the 8-flow is `φ₁ + 2φ₂ + 4φ₃` from Eulerian orientations of the three even subgraphs.

Tutte's theorem and Seymour's 6-flow theorem (version 3) are proved in `SixFlowLib/`
(namespace `SixFlow`): the integer lift minimises the total vertex excess and corrects it
by multiples of `k` along paths; the 6-flow is obtained as a nowhere-zero
`ℤ/2 × ℤ/3`-flow by Seymour's greedy construction on an internal multigraph model, after
splitting empty cuts and contracting one edge of each 2-edge cut, and is converted with the
Chinese remainder theorem and Tutte's theorem. The definition `IsNowhereZeroGroupFlow` is the
library's own and is reproduced verbatim in `Challenge.lean`.
-/

@[expose] public section

open Finset SimpleGraph

namespace JaegerFlow

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `φ` is a nowhere-zero integer `k`-flow on `G`: it is antisymmetric on darts, satisfies
`0 < |φ d| < k` on every dart, and is conserved at every vertex. -/
def IsNowhereZeroFlow (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (φ : G.Dart → ℤ) :
    Prop :=
  (∀ d, φ d.symm = -φ d) ∧ (∀ d, φ d ≠ 0 ∧ |φ d| < k) ∧
    ∀ v, ∑ d ∈ univ.filter (fun d : G.Dart ↦ d.fst = v), φ d = 0

omit [DecidableEq V] in
/-- **Two disjoint spanning trees give a cover by two even subgraphs.** If `G` contains two
edge-disjoint spanning trees `T₁` and `T₂`, then there are subgraphs `H₁, H₂ ≤ G` with
`H₁ ⊔ H₂ = G` in which every vertex has even degree. -/
theorem exists_even_cover_of_trees (G : SimpleGraph V) (T₁ T₂ : SimpleGraph V)
    (h₁ : T₁ ≤ G) (h₂ : T₂ ≤ G) (ht₁ : T₁.IsTree) (ht₂ : T₂.IsTree) (hT : Disjoint T₁ T₂) :
    ∃ H₁ H₂ : SimpleGraph V, ∃ _ : DecidableRel H₁.Adj, ∃ _ : DecidableRel H₂.Adj,
      H₁ ≤ G ∧ H₂ ≤ G ∧ H₁ ⊔ H₂ = G ∧ (∀ v, Even (H₁.degree v)) ∧ ∀ v, Even (H₂.degree v) :=
  Jaeger.exists_even_cover_of_trees G T₁ T₂ h₁ h₂ ht₁ ht₂ hT

/-- **Two disjoint spanning trees give a nowhere-zero 4-flow.** If `G` contains two edge-disjoint
spanning trees, then `G` has a nowhere-zero integer 4-flow. -/
theorem exists_flow_of_trees (G : SimpleGraph V) [DecidableRel G.Adj] (T₁ T₂ : SimpleGraph V)
    (h₁ : T₁ ≤ G) (h₂ : T₂ ≤ G) (ht₁ : T₁.IsTree) (ht₂ : T₂.IsTree) (hT : Disjoint T₁ T₂) :
    ∃ φ : G.Dart → ℤ, IsNowhereZeroFlow G 4 φ :=
  Jaeger.exists_flow_of_trees G T₁ T₂ h₁ h₂ ht₁ ht₂ hT

/-- **Jaeger's 4-flow theorem.** Every finite 4-edge-connected graph has a nowhere-zero integer
4-flow. -/
theorem jaeger_four_flow (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsEdgeConnected 4) :
    ∃ φ : G.Dart → ℤ, IsNowhereZeroFlow G 4 φ :=
  Jaeger.jaeger_four_flow G hG

end JaegerFlow

/-! ### Jaeger's 8-flow theorem (version 2) -/

namespace EightFlowTheorem

open JaegerFlow

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- A bridgeless finite graph is covered by three even subgraphs. -/
theorem exists_even_cover_three (G : SimpleGraph V) (hG : ∀ e ∈ G.edgeSet, ¬ G.IsBridge e) :
    ∃ H : Fin 3 → SimpleGraph V, ∃ _ : ∀ i, DecidableRel (H i).Adj,
      (∀ i, H i ≤ G) ∧ (⨆ i, H i) = G ∧ ∀ i v, Even ((H i).degree v) :=
  EightFlow.exists_even_cover_three G hG

/-- **Jaeger's 8-flow theorem.** Every finite bridgeless graph has a nowhere-zero integer
8-flow. -/
theorem jaeger_eight_flow (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : ∀ e ∈ G.edgeSet, ¬ G.IsBridge e) :
    ∃ φ : G.Dart → ℤ, IsNowhereZeroFlow G 8 φ :=
  EightFlow.jaeger_eight_flow G hG

/-- A graph with a nowhere-zero `k`-flow has no bridge. -/
theorem not_isBridge_of_flow (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} {φ : G.Dart → ℤ}
    (hφ : IsNowhereZeroFlow G k φ) : ∀ e ∈ G.edgeSet, ¬ G.IsBridge e :=
  EightFlow.not_isBridge_of_flow G hφ

end EightFlowTheorem

/-! ### Tutte's group-to-integer theorem and Seymour's 6-flow theorem (version 3) -/

namespace SixFlowTheorem

open SixFlow

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Tutte (1949).** A nowhere-zero `ℤ/k`-flow lifts to a nowhere-zero integer `k`-flow. -/
theorem integer_flow_of_zmod (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (hk : 0 < k)
    (h : ∃ φ : G.Dart → ZMod k, IsNowhereZeroGroupFlow G φ) :
    ∃ ψ : G.Dart → ℤ, JaegerFlow.IsNowhereZeroFlow G k ψ :=
  SixFlow.integer_flow_of_zmod G hk h

/-- A nowhere-zero integer `k`-flow reduces modulo `k` to a nowhere-zero `ℤ/k`-flow. -/
theorem zmod_flow_of_integer (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ}
    (h : ∃ ψ : G.Dart → ℤ, JaegerFlow.IsNowhereZeroFlow G k ψ) :
    ∃ φ : G.Dart → ZMod k, IsNowhereZeroGroupFlow G φ :=
  SixFlow.zmod_flow_of_integer G h

/-- **Seymour's 6-flow theorem (1981).** Every finite bridgeless graph has a nowhere-zero integer
6-flow. -/
theorem seymour_six_flow (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : ∀ e ∈ G.edgeSet, ¬ G.IsBridge e) :
    ∃ φ : G.Dart → ℤ, JaegerFlow.IsNowhereZeroFlow G 6 φ :=
  SixFlow.seymour_six_flow G hG

end SixFlowTheorem
