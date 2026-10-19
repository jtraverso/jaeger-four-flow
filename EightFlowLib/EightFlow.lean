/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import JaegerLib.Jaeger
public import EightFlowLib.CaseAnalysis

/-!
# Jaeger's 8-flow theorem

For a finite simple graph `G` with no bridge (Mathlib's `SimpleGraph.IsBridge`):

* `EightFlow.exists_even_cover_three`: the edges of `G` are covered by three subgraphs in which
  every vertex has even degree.
* `EightFlow.jaeger_eight_flow`: **Jaeger's 8-flow theorem (Jaeger 1979; Kilpatrick 1975).** `G`
  has a nowhere-zero integer 8-flow (`Jaeger.IsNowhereZeroFlow G 8`).
* `EightFlow.not_isBridge_of_flow`: conversely, an edge carrying a nonzero value of a flow is not
  a bridge; so a graph with a nowhere-zero flow is bridgeless.
-/

@[expose] public section

open Finset SimpleGraph

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace EightFlow

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
lemma zmod2_eq_one_of_ne_zero {x : ZMod 2} (h : x ≠ 0) : x = 1 := by
  fin_cases x
  · exact absurd rfl h
  · rfl

/-- A dart function as a function on ordered pairs of vertices. -/
lemma isFl_of_dart (G : SimpleGraph V) [DecidableRel G.Adj] {φ : G.Dart → ℤ}
    (ha : ∀ d, φ d.symm = -φ d)
    (hc : ∀ v, ∑ d ∈ univ.filter (fun d : G.Dart ↦ d.fst = v), φ d = 0) :
    IsFl G (fun x y => if h : G.Adj x y then φ ⟨(x, y), h⟩ else 0) := by
  classical
  refine ⟨fun u v => ?_, fun u v huv => by simp [huv], fun x => ?_⟩
  · dsimp only
    by_cases h : G.Adj u v
    · rw [dite_eq_left h, dite_eq_left h.symm]
      exact ha ⟨(u, v), h⟩
    · rw [dite_eq_right h, dite_eq_right (fun h' => h h'.symm), neg_zero]
  · dsimp only
    rw [← Finset.sum_filter_of_ne (p := fun y => G.Adj x y) (fun y _ hy => by
      by_contra h; exact hy (dite_eq_right h))]
    refine Eq.trans ?_ (hc x)
    refine (Finset.sum_bij' (fun d _ => d.snd) (fun y hy => ⟨(x, y), (mem_filter.mp hy).2⟩)
      ?_ ?_ ?_ ?_ ?_).symm
    · intro d hd
      rw [mem_filter] at hd ⊢
      exact ⟨mem_univ _, hd.2 ▸ d.adj⟩
    · intro y hy
      simp
    · intro d hd
      rw [mem_filter] at hd
      ext
      · exact hd.2.symm
      · rfl
    · intro y hy
      rfl
    · intro d hd
      rw [mem_filter] at hd
      obtain ⟨⟨a, b⟩, hab⟩ := d
      obtain ⟨-, rfl⟩ := hd
      dsimp only
      rw [dite_eq_left hab]

omit [DecidableEq V] in
/-- A bridgeless finite graph is covered by three even subgraphs. -/
theorem exists_even_cover_three (G : SimpleGraph V) (hG : ∀ e ∈ G.edgeSet, ¬ G.IsBridge e) :
    ∃ H : Fin 3 → SimpleGraph V, ∃ _ : ∀ i, DecidableRel (H i).Adj,
      (∀ i, H i ≤ G) ∧ (⨆ i, H i) = G ∧ ∀ i v, Even ((H i).degree v) := by
  classical
  obtain ⟨ℓ, hℓ, hn⟩ := gl_of_bl G (bl_of_bridgeless hG)
  let H : Fin 3 → SimpleGraph V := fun i =>
    { Adj := fun u v => G.Adj u v ∧ ℓ u v i ≠ 0
      symm := ⟨fun u v h => ⟨h.1.symm, by
        rw [hℓ.1, neg_eq_of_add_self m3_add_self]; exact h.2⟩⟩
      loopless := ⟨fun v h => G.irrefl h.1⟩ }
  refine ⟨H, fun i => Classical.decRel _, fun i u v h => h.1, ?_, fun i v => ?_⟩
  · refine le_antisymm (iSup_le fun i u v h => h.1) fun u v huv => ?_
    rw [iSup_adj]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp (hn u v huv)
    exact ⟨i, huv, hi⟩
  · rw [← ZMod.natCast_eq_zero_iff_even, Jaeger.degree_cast_zmod]
    have h0 : (∑ w, ℓ v w) i = 0 := by rw [hℓ.2.2 v]; rfl
    rw [Finset.sum_apply] at h0
    refine (sum_congr rfl fun w _ => ?_).trans h0
    by_cases h : (H i).Adj v w
    · rw [ite_eq_left h]
      exact (zmod2_eq_one_of_ne_zero h.2).symm
    · rw [ite_eq_right h]
      by_cases hg : G.Adj v w
      · exact (not_not.mp fun h' => h ⟨hg, h'⟩).symm
      · rw [hℓ.2.1 v w hg]; rfl

/-- **Jaeger's 8-flow theorem.** Every finite bridgeless graph has a nowhere-zero integer
8-flow. -/
theorem jaeger_eight_flow (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : ∀ e ∈ G.edgeSet, ¬ G.IsBridge e) :
    ∃ φ : G.Dart → ℤ, Jaeger.IsNowhereZeroFlow G 8 φ := by
  obtain ⟨H, inst, hle, hsup, heven⟩ := exists_even_cover_three G hG
  obtain ⟨ψ₀, a₀, v₀, n₀, c₀⟩ := @Jaeger.exists_dart_fun V _ _ G (H 0) _ (inst 0) (hle 0) (heven 0)
  obtain ⟨ψ₁, a₁, v₁, n₁, c₁⟩ := @Jaeger.exists_dart_fun V _ _ G (H 1) _ (inst 1) (hle 1) (heven 1)
  obtain ⟨ψ₂, a₂, v₂, n₂, c₂⟩ := @Jaeger.exists_dart_fun V _ _ G (H 2) _ (inst 2) (hle 2) (heven 2)
  refine ⟨fun d => ψ₀ d + 2 * ψ₁ d + 4 * ψ₂ d, fun d => ?_, fun d => ?_, fun v => ?_⟩
  · simp only [a₀, a₁, a₂]
    ring
  · have hadj : ∃ i, (H i).Adj d.fst d.snd := by
      rw [← iSup_adj, hsup]
      exact d.adj
    rw [abs_lt]
    push_cast
    obtain ⟨i, hi⟩ := hadj
    fin_cases i
    · have := n₀ d hi
      rcases v₀ d with h0 | h0 | h0 <;> rcases v₁ d with h1 | h1 | h1 <;>
        rcases v₂ d with h2 | h2 | h2 <;> omega
    · have := n₁ d hi
      rcases v₀ d with h0 | h0 | h0 <;> rcases v₁ d with h1 | h1 | h1 <;>
        rcases v₂ d with h2 | h2 | h2 <;> omega
    · have := n₂ d hi
      rcases v₀ d with h0 | h0 | h0 <;> rcases v₁ d with h1 | h1 | h1 <;>
        rcases v₂ d with h2 | h2 | h2 <;> omega
  · rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      c₀ v, c₁ v, c₂ v]
    ring

/-- A graph with a nowhere-zero `k`-flow has no bridge. -/
theorem not_isBridge_of_flow (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} {φ : G.Dart → ℤ}
    (hφ : Jaeger.IsNowhereZeroFlow G k φ) : ∀ e ∈ G.edgeSet, ¬ G.IsBridge e := by
  classical
  intro e he hbr
  induction e using Sym2.ind with
  | _ u v =>
  have huv : G.Adj u v := he
  rw [isBridge_iff] at hbr
  have hf := isFl_of_dart G hφ.1 hφ.2.2
  let R : Finset V := univ.filter fun w => (G.deleteEdges {s(u, v)}).Reachable u w
  have hX : X G R = {(u, v)} := by
    ext ⟨x, y⟩
    rw [mem_X, mem_singleton]
    simp only [R, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨hx, hy, hxy⟩
      by_cases he' : s(x, y) = s(u, v)
      · rcases Sym2.eq_iff.mp he' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rfl
        · exact absurd hx hbr
      · exact absurd (hx.trans (Adj.reachable (by
          rw [deleteEdges_adj]; exact ⟨hxy, by simpa using he'⟩))) hy
    · rintro ⟨⟩
      exact ⟨Reachable.refl _, hbr, huv⟩
  have := cut_sum_X (M := ℤ) hf R
  rw [hX, sum_singleton] at this
  simp only [dite_eq_left huv] at this
  exact (hφ.2.1 _).1 this

end EightFlow
