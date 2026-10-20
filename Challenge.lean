/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# Jaeger's 4-flow theorem

A *nowhere-zero integer `k`-flow* on a finite simple graph `G` is a function `φ` on the darts
(oriented edges) of `G` such that `φ (d.symm) = -φ d`, `0 < |φ d| < k` for every dart `d`, and the
flow is conserved at every vertex: `∑_{d.fst = v} φ d = 0`.

* `JaegerFlow.exists_even_cover_of_trees`: if `G` contains two edge-disjoint spanning trees, then the
  edges of `G` are covered by two even subgraphs (every vertex has even degree in each of them),
  i.e. `G` has a nowhere-zero `ℤ₂ × ℤ₂`-flow.
* `JaegerFlow.exists_flow_of_trees`: if `G` contains two edge-disjoint spanning trees, then `G` has a
  nowhere-zero integer 4-flow.
* `JaegerFlow.jaeger_four_flow`: **Jaeger (1979).** Every finite 4-edge-connected graph has a
  nowhere-zero integer 4-flow.

Reference: F. Jaeger, *Flows and generalized coloring theorems in graphs*, J. Combin. Theory
Ser. B 26 (1979) 205–216.

**Version 2: Jaeger's 8-flow theorem.** For a finite simple graph `G` with no bridge (Mathlib's
`SimpleGraph.IsBridge`):

* `EightFlowTheorem.exists_even_cover_three`: the edges of `G` are covered by three subgraphs in
  which every vertex has even degree.
* `EightFlowTheorem.jaeger_eight_flow`: **Jaeger's 8-flow theorem (Jaeger 1979; Kilpatrick
  1975).** `G` has a nowhere-zero integer 8-flow.
* `EightFlowTheorem.not_isBridge_of_flow`: conversely, a graph with a nowhere-zero flow has no
  bridge.

**Version 3: Tutte's group-to-integer theorem and Seymour's 6-flow theorem.** A nowhere-zero
`A`-flow (`SixFlow.IsNowhereZeroGroupFlow`, stated below verbatim with the same name as in the
library) is an antisymmetric, nowhere-zero, conserved function on darts with values in an abelian
group `A`.

* `SixFlowTheorem.integer_flow_of_zmod`: **Tutte (1949).** For `k > 0`, a nowhere-zero
  `ℤ/k`-flow lifts to a nowhere-zero integer `k`-flow.
* `SixFlowTheorem.zmod_flow_of_integer`: conversely, a nowhere-zero integer `k`-flow reduces to a
  nowhere-zero `ℤ/k`-flow.
* `SixFlowTheorem.seymour_six_flow`: **Seymour's 6-flow theorem (1981).** Every finite
  bridgeless graph has a nowhere-zero integer 6-flow.

The Mathlib definitions used in these statements are reproduced verbatim, with file and line at the
pinned Mathlib revision, in `MATHLIB_DEFINITIONS.md` at the root of this repository.
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
      H₁ ≤ G ∧ H₂ ≤ G ∧ H₁ ⊔ H₂ = G ∧ (∀ v, Even (H₁.degree v)) ∧ ∀ v, Even (H₂.degree v) := by
  sorry

/-- **Two disjoint spanning trees give a nowhere-zero 4-flow.** If `G` contains two edge-disjoint
spanning trees, then `G` has a nowhere-zero integer 4-flow. -/
theorem exists_flow_of_trees (G : SimpleGraph V) [DecidableRel G.Adj] (T₁ T₂ : SimpleGraph V)
    (h₁ : T₁ ≤ G) (h₂ : T₂ ≤ G) (ht₁ : T₁.IsTree) (ht₂ : T₂.IsTree) (hT : Disjoint T₁ T₂) :
    ∃ φ : G.Dart → ℤ, IsNowhereZeroFlow G 4 φ := by
  sorry

/-- **Jaeger's 4-flow theorem.** Every finite 4-edge-connected graph has a nowhere-zero integer
4-flow. -/
theorem jaeger_four_flow (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsEdgeConnected 4) :
    ∃ φ : G.Dart → ℤ, IsNowhereZeroFlow G 4 φ := by
  sorry

end JaegerFlow

/-! ### Jaeger's 8-flow theorem (version 2) -/

namespace EightFlowTheorem

open JaegerFlow

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- A bridgeless finite graph is covered by three even subgraphs. -/
theorem exists_even_cover_three (G : SimpleGraph V) (hG : ∀ e ∈ G.edgeSet, ¬ G.IsBridge e) :
    ∃ H : Fin 3 → SimpleGraph V, ∃ _ : ∀ i, DecidableRel (H i).Adj,
      (∀ i, H i ≤ G) ∧ (⨆ i, H i) = G ∧ ∀ i v, Even ((H i).degree v) := by
  sorry

/-- **Jaeger's 8-flow theorem.** Every finite bridgeless graph has a nowhere-zero integer
8-flow. -/
theorem jaeger_eight_flow (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : ∀ e ∈ G.edgeSet, ¬ G.IsBridge e) :
    ∃ φ : G.Dart → ℤ, IsNowhereZeroFlow G 8 φ := by
  sorry

/-- A graph with a nowhere-zero `k`-flow has no bridge. -/
theorem not_isBridge_of_flow (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} {φ : G.Dart → ℤ}
    (hφ : IsNowhereZeroFlow G k φ) : ∀ e ∈ G.edgeSet, ¬ G.IsBridge e := by
  sorry

end EightFlowTheorem

/-! ### Group flows (version 3): definition, verbatim from `SixFlowLib/SixFlow.lean` -/

namespace SixFlow

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `φ` is a nowhere-zero `A`-flow on `G`: antisymmetric on darts, nonzero on every dart, and
conserved at every vertex. -/
def IsNowhereZeroGroupFlow {A : Type*} [AddCommGroup A] (G : SimpleGraph V) [DecidableRel G.Adj]
    (φ : G.Dart → A) : Prop :=
  (∀ d, φ d.symm = -φ d) ∧ (∀ d, φ d ≠ 0) ∧
    ∀ v, ∑ d ∈ univ.filter (fun d : G.Dart ↦ d.fst = v), φ d = 0

end SixFlow

/-! ### Tutte's group-to-integer theorem and Seymour's 6-flow theorem (version 3) -/

namespace SixFlowTheorem

open SixFlow

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Tutte (1949).** A nowhere-zero `ℤ/k`-flow lifts to a nowhere-zero integer `k`-flow. -/
theorem integer_flow_of_zmod (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (hk : 0 < k)
    (h : ∃ φ : G.Dart → ZMod k, IsNowhereZeroGroupFlow G φ) :
    ∃ ψ : G.Dart → ℤ, JaegerFlow.IsNowhereZeroFlow G k ψ := by
  sorry

/-- A nowhere-zero integer `k`-flow reduces modulo `k` to a nowhere-zero `ℤ/k`-flow. -/
theorem zmod_flow_of_integer (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ}
    (h : ∃ ψ : G.Dart → ℤ, JaegerFlow.IsNowhereZeroFlow G k ψ) :
    ∃ φ : G.Dart → ZMod k, IsNowhereZeroGroupFlow G φ := by
  sorry

/-- **Seymour's 6-flow theorem (1981).** Every finite bridgeless graph has a nowhere-zero integer
6-flow. -/
theorem seymour_six_flow (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : ∀ e ∈ G.edgeSet, ¬ G.IsBridge e) :
    ∃ φ : G.Dart → ℤ, JaegerFlow.IsNowhereZeroFlow G 6 φ := by
  sorry

end SixFlowTheorem
