/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import TreePackingLib.NashWilliams
public import Euler.Orientation
public import JaegerLib.JaegerAux

/-!
# Jaeger's 4-flow theorem

A *nowhere-zero integer `k`-flow* on a finite simple graph `G` is a function `φ` on the darts
(oriented edges) of `G` such that `φ (d.symm) = -φ d`, `0 < |φ d| < k` for every dart `d`, and the
flow is conserved at every vertex: `∑_{d.fst = v} φ d = 0`.

* `Jaeger.exists_even_cover_of_trees`: if `G` contains two edge-disjoint spanning trees, then the
  edges of `G` are covered by two even subgraphs (every vertex has even degree in each of them),
  i.e. `G` has a nowhere-zero `ℤ₂ × ℤ₂`-flow.
* `Jaeger.exists_flow_of_trees`: if `G` contains two edge-disjoint spanning trees, then `G` has a
  nowhere-zero integer 4-flow.
* `Jaeger.jaeger_four_flow`: **Jaeger (1979).** Every finite 4-edge-connected graph has a
  nowhere-zero integer 4-flow.

Reference: F. Jaeger, *Flows and generalized coloring theorems in graphs*, J. Combin. Theory
Ser. B 26 (1979) 205–216.
-/

@[expose] public section

open Finset SimpleGraph

namespace Jaeger

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
  classical
  have key : ∀ T : SimpleGraph V, T ≤ G → T.IsTree → ∃ H : SimpleGraph V,
      ∃ _ : DecidableRel H.Adj, H ≤ G ∧ G \ T ≤ H ∧ ∀ v, Even (H.degree v) := by
    intro T hTG hTt
    obtain ⟨n, hn⟩ := even_card_odd_degree_vertices (G \ T)
    obtain ⟨J, hJT, _, hJ⟩ := exists_tJoin T hTt.connected n
      (univ.filter fun v => Odd ((G \ T).degree v)) (by rw [hn]; ring)
    refine ⟨symmDiff (G \ T) J, inferInstance,
      symmDiff_le_sup.trans (sup_le sdiff_le (hJT.trans hTG)), fun a b hab => ?_, fun v => ?_⟩
    · have hJ' : ¬ J.Adj a b := fun h => hab.2 (hJT h)
      simp only [symmDiff, sup_adj, sdiff_adj]
      exact Or.inl ⟨hab, hJ'⟩
    · rw [← ZMod.natCast_eq_zero_iff_even, degree_symmDiff_zmod,
        natCast_zmod_two_eq_ite (hJ v),
        natCast_zmod_two_eq_ite (P := v ∈ univ.filter fun v => Odd ((G \ T).degree v))
          (by simp)]
      split_ifs <;> rfl
  obtain ⟨H₁, i₁, hH₁G, hGH₁, he₁⟩ := key T₁ h₁ ht₁
  obtain ⟨H₂, i₂, hH₂G, hGH₂, he₂⟩ := key T₂ h₂ ht₂
  refine ⟨H₁, H₂, i₁, i₂, hH₁G, hH₂G, le_antisymm (sup_le hH₁G hH₂G) fun a b hab => ?_, he₁, he₂⟩
  by_cases ht : T₁.Adj a b
  · have ht' : ¬ T₂.Adj a b := fun h => hT.le_bot (show (T₁ ⊓ T₂).Adj a b from ⟨ht, h⟩)
    exact Or.inr (hGH₂ ⟨hab, ht'⟩)
  · exact Or.inl (hGH₁ ⟨hab, ht⟩)

/-- **Two disjoint spanning trees give a nowhere-zero 4-flow.** If `G` contains two edge-disjoint
spanning trees, then `G` has a nowhere-zero integer 4-flow. -/
theorem exists_flow_of_trees (G : SimpleGraph V) [DecidableRel G.Adj] (T₁ T₂ : SimpleGraph V)
    (h₁ : T₁ ≤ G) (h₂ : T₂ ≤ G) (ht₁ : T₁.IsTree) (ht₂ : T₂.IsTree) (hT : Disjoint T₁ T₂) :
    ∃ φ : G.Dart → ℤ, IsNowhereZeroFlow G 4 φ := by
  obtain ⟨H₁, H₂, i₁, i₂, hH₁, hH₂, hsup, he₁, he₂⟩ :=
    exists_even_cover_of_trees G T₁ T₂ h₁ h₂ ht₁ ht₂ hT
  obtain ⟨ψ₁, a₁, v₁, n₁, c₁⟩ := exists_dart_fun G H₁ hH₁ he₁
  obtain ⟨ψ₂, a₂, v₂, n₂, c₂⟩ := exists_dart_fun G H₂ hH₂ he₂
  refine ⟨fun d => ψ₁ d + 2 * ψ₂ d, fun d => ?_, fun d => ?_, fun v => ?_⟩
  · simp only [a₁, a₂]
    ring
  · have hadj : H₁.Adj d.fst d.snd ∨ H₂.Adj d.fst d.snd := by
      rw [← sup_adj, hsup]
      exact d.adj
    rw [abs_lt]
    push_cast
    rcases hadj with h | h
    · have := n₁ d h
      rcases v₁ d with h1 | h1 | h1 <;> rcases v₂ d with h2 | h2 | h2 <;> omega
    · have := n₂ d h
      rcases v₁ d with h1 | h1 | h1 <;> rcases v₂ d with h2 | h2 | h2 <;> omega
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum, c₁ v, c₂ v]
    ring

/-- **Jaeger's 4-flow theorem.** Every finite 4-edge-connected graph has a nowhere-zero integer
4-flow. -/
theorem jaeger_four_flow (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsEdgeConnected 4) :
    ∃ φ : G.Dart → ℤ, IsNowhereZeroFlow G 4 φ := by
  rcases isEmpty_or_nonempty V with hV | hV
  · exact ⟨fun _ => 0, fun d => isEmptyElim d.fst, fun d => isEmptyElim d.fst,
      fun v => isEmptyElim v⟩
  · obtain ⟨T, hT, hdisj⟩ := NashWilliams.exists_trees_of_isEdgeConnected G 2 hG
    exact exists_flow_of_trees G (T 0) (T 1) (hT 0).1 (hT 1).1 (hT 0).2 (hT 1).2
      (hdisj (by decide))

end Jaeger
