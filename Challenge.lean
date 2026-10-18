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
