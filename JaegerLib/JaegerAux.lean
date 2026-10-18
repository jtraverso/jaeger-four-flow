/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import Euler.Orientation

/-!
# Auxiliary lemmas for Jaeger's 4-flow theorem

* parity of degrees, computed in `ZMod 2`, and its behaviour under symmetric difference;
* `Jaeger.exists_tJoin`: in a connected graph `T`, every vertex set `W` of even cardinality is the
  set of odd-degree vertices of some subgraph `J ≤ T` (a `W`-join);
* `Jaeger.exists_dart_fun`: a balanced orientation of an even subgraph `H ≤ G` gives an
  antisymmetric, conserved function `G.Dart → ℤ` with values in `{-1, 0, 1}`, nonzero exactly on
  the darts of `H`.
-/

@[expose] public section

open Finset SimpleGraph

namespace Jaeger

variable {V : Type*} [Fintype V]

/-- The degree modulo `2`, as a sum of indicators. -/
lemma degree_cast_zmod (A : SimpleGraph V) [DecidableRel A.Adj] (v : V) :
    (A.degree v : ZMod 2) = ∑ x, if A.Adj v x then 1 else 0 := by
  rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter, Finset.natCast_card_filter]

/-- Degrees in a symmetric difference add modulo `2`. -/
lemma degree_symmDiff_zmod (A B : SimpleGraph V) [DecidableRel A.Adj] [DecidableRel B.Adj]
    [DecidableRel (symmDiff A B).Adj] (v : V) :
    ((symmDiff A B).degree v : ZMod 2) = A.degree v + B.degree v := by
  simp only [degree_cast_zmod, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  have : (symmDiff A B).Adj v x ↔ (A.Adj v x ∧ ¬ B.Adj v x) ∨ (B.Adj v x ∧ ¬ A.Adj v x) := by
    simp [symmDiff]
  by_cases ha : A.Adj v x <;> by_cases hb : B.Adj v x <;>
    simp only [this, ha, hb, ite_true, ite_false, not_true, not_false_eq_true, and_true,
      and_false, or_false, false_or, add_zero, zero_add]
  rfl

lemma natCast_zmod_two_eq_ite {n : ℕ} {P : Prop} [Decidable P] (h : Odd n ↔ P) :
    (n : ZMod 2) = if P then 1 else 0 := by
  split_ifs with hP
  · exact ZMod.natCast_eq_one_iff_odd.mpr (h.mpr hP)
  · exact ZMod.natCast_eq_zero_iff_even.mpr (Nat.not_odd_iff_even.mp (fun ho => hP (h.mp ho)))

omit [Fintype V] in
/-- The graph formed by the edges of a walk. -/
lemma walkGraph_le {T : SimpleGraph V} {u w : V} (p : T.Walk u w) :
    fromEdgeSet {e | e ∈ p.edges} ≤ T := by
  intro a b h
  rw [fromEdgeSet_adj] at h
  exact p.edges_subset_edgeSet h.1

/-- In the graph formed by the edges of a path from `u` to `w ≠ u`, exactly `u` and `w` have odd
degree. -/
lemma odd_degree_walkGraph_iff {T : SimpleGraph V} {u w : V} (p : T.Walk u w)
    (hp : p.IsPath) (huw : u ≠ w) [DecidableRel (fromEdgeSet {e | e ∈ p.edges}).Adj] (x : V) :
    Odd ((fromEdgeSet {e | e ∈ p.edges}).degree x) ↔ x = u ∨ x = w := by
  classical
  rw [← card_incidenceFinset_eq_degree]
  have hinc : (fromEdgeSet {e | e ∈ p.edges}).incidenceFinset x =
      p.edges.toFinset.filter (fun e => x ∈ e) := by
    ext e
    rw [mem_incidenceFinset, Finset.mem_filter, List.mem_toFinset]
    simp only [incidenceSet, edgeSet_fromEdgeSet]
    change (e ∈ _ ∧ _) ↔ _
    rw [Set.mem_sdiff]
    constructor
    · rintro ⟨⟨h1, -⟩, h2⟩
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, T.not_isDiag_of_mem_edgeSet (p.edges_subset_edgeSet h1)⟩, h2⟩
  rw [hinc, SimpleGraph.card_filter_toFinset_of_nodup hp.isTrail.edges_nodup]
  have := hp.isTrail.even_countP_edges_iff x
  rw [← Nat.not_even_iff_odd, this]
  tauto

/-- **`W`-joins in a connected graph.** If `T` is connected and `#W` is even, there is `J ≤ T`
whose odd-degree vertices are exactly the vertices of `W`. -/
lemma exists_tJoin (T : SimpleGraph V) (hT : T.Connected) :
    ∀ n, ∀ W : Finset V, #W = 2 * n → ∃ J : SimpleGraph V, J ≤ T ∧
      ∃ _ : DecidableRel J.Adj, ∀ v, (Odd (J.degree v) ↔ v ∈ W) := by
  classical
  intro n
  induction n with
  | zero =>
    intro W hW
    rw [mul_zero, Finset.card_eq_zero] at hW
    subst hW
    exact ⟨⊥, bot_le, inferInstance, fun v => by simp⟩
  | succ n ih =>
    intro W hW
    obtain ⟨u, hu⟩ : W.Nonempty := Finset.card_pos.mp (by omega)
    have h1 : #(W.erase u) = 2 * n + 1 := by rw [Finset.card_erase_of_mem hu]; omega
    obtain ⟨w, hw⟩ : (W.erase u).Nonempty := Finset.card_pos.mp (by omega)
    have h2 : #((W.erase u).erase w) = 2 * n := by rw [Finset.card_erase_of_mem hw]; omega
    obtain ⟨J', hJ', _, hJ'odd⟩ := ih _ h2
    have huw : u ≠ w := fun h => by simp [h] at hw
    obtain ⟨p, hp⟩ := (hT.preconnected u w).exists_isPath
    refine ⟨symmDiff J' (fromEdgeSet {e | e ∈ p.edges}),
      symmDiff_le_sup.trans (sup_le hJ' (walkGraph_le p)), inferInstance, fun v => ?_⟩
    rw [← ZMod.natCast_eq_one_iff_odd, degree_symmDiff_zmod,
      natCast_zmod_two_eq_ite (hJ'odd v), natCast_zmod_two_eq_ite
        (odd_degree_walkGraph_iff p hp huw v)]
    have hmem : v ∈ (W.erase u).erase w ↔ v ≠ w ∧ v ≠ u ∧ v ∈ W := by simp
    have hwW : w ∈ W := Finset.mem_of_mem_erase hw
    by_cases hvu : v = u
    · subst hvu; simp [hu, huw]
    by_cases hvw : v = w
    · subst hvw; simp [hwW, Ne.symm huw]
    simp [hvu, hvw]

/-- **Signed indicator of a balanced orientation.** If every vertex has even degree in `H ≤ G`,
there is an antisymmetric, conserved function on the darts of `G` with values in `{-1, 0, 1}`
which is nonzero on every dart of `H`. -/
lemma exists_dart_fun [DecidableEq V] (G H : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel H.Adj] (hle : H ≤ G) (heven : ∀ v, Even (H.degree v)) :
    ∃ ψ : G.Dart → ℤ, (∀ d, ψ d.symm = -ψ d) ∧ (∀ d, ψ d = -1 ∨ ψ d = 0 ∨ ψ d = 1) ∧
      (∀ d, H.Adj d.fst d.snd → ψ d ≠ 0) ∧
      ∀ v, ∑ d ∈ univ.filter (fun d : G.Dart ↦ d.fst = v), ψ d = 0 := by
  obtain ⟨Ds, hinj, hbal, hcov⟩ := H.exists_balanced_orientation heven
  let m : H.Dart → G.Dart := (Hom.ofLE hle).mapDart
  have hm_edge : ∀ e, (m e).edge = e.edge := fun e => rfl
  have hm_fst : ∀ e, (m e).fst = e.fst := fun e => rfl
  have hm_snd : ∀ e, (m e).snd = e.snd := fun e => rfl
  have hm_inj : Function.Injective m := by
    intro e e' h
    have h1 := congrArg (fun d : G.Dart => d.fst) h
    have h2 := congrArg (fun d : G.Dart => d.snd) h
    rw [hm_fst, hm_fst] at h1
    rw [hm_snd, hm_snd] at h2
    exact Dart.ext _ _ (Prod.ext h1 h2)
  let a : G.Dart → ℕ := fun d => #(Ds.filter (fun e => m e = d))
  have ha_le : ∀ d, a d ≤ 1 := by
    intro d
    refine Finset.card_le_one.mpr fun e he e' he' => hm_inj ?_
    simp only [Finset.mem_filter] at he he'
    rw [he.2, he'.2]
  have hab : ∀ d, ¬ (a d = 1 ∧ a d.symm = 1) := by
    rintro d ⟨h1, h2⟩
    obtain ⟨e, he⟩ := Finset.card_eq_one.mp h1
    obtain ⟨e', he'⟩ := Finset.card_eq_one.mp h2
    have hes : e ∈ Ds ∧ m e = d := by
      simpa using (Finset.ext_iff.mp he e).mpr (Finset.mem_singleton_self e)
    have hes' : e' ∈ Ds ∧ m e' = d.symm := by
      simpa using (Finset.ext_iff.mp he' e').mpr (Finset.mem_singleton_self e')
    have hedge : e.edge = e'.edge := by
      rw [← hm_edge, ← hm_edge, hes.2, hes'.2, Dart.edge_symm]
    have := hinj e hes.1 e' hes'.1 hedge
    subst this
    exact d.symm_ne (hes'.2.symm.trans hes.2)
  have hcov' : ∀ d, H.Adj d.fst d.snd → 1 ≤ a d + a d.symm := by
    intro d hd
    obtain ⟨e, heD, he⟩ := hcov s(d.fst, d.snd) hd
    have : (m e).edge = d.edge := by rw [hm_edge, he]; rfl
    rcases (dart_edge_eq_iff _ _).mp this with h | h
    · have : 1 ≤ a d := Finset.card_pos.mpr ⟨e, by simp [heD, h]⟩
      omega
    · have : 1 ≤ a d.symm := Finset.card_pos.mpr ⟨e, by simp [heD, h]⟩
      omega
  refine ⟨fun d => (a d : ℤ) - a d.symm, fun d => by simp, fun d => ?_, fun d hd => ?_,
    fun v => ?_⟩
  · dsimp only
    have := ha_le d
    have := ha_le d.symm
    have := hab d
    omega
  · dsimp only
    have := ha_le d
    have := ha_le d.symm
    have := hcov' d hd
    have := hab d
    omega
  · rw [Finset.sum_sub_distrib, sub_eq_zero]
    have e1 : ∑ d ∈ univ.filter (fun d : G.Dart ↦ d.fst = v), (a d : ℤ) =
        #(Ds.filter (fun e => e.fst = v)) := by
      rw [card_eq_sum_card_fiberwise (f := m) (t := univ.filter (fun d : G.Dart => d.fst = v))]
      · push_cast
        refine sum_congr rfl fun d hd => ?_
        norm_cast
        change #(Ds.filter fun e => m e = _) = _
        congr 1
        ext e
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd ⊢
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨⟨h1, by rw [← hm_fst, h2, hd]⟩, h2⟩
        · rintro ⟨⟨h1, -⟩, h2⟩
          exact ⟨h1, h2⟩
      · intro e he
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at he ⊢
        exact he.2
    have e2 : ∑ d ∈ univ.filter (fun d : G.Dart ↦ d.fst = v), (a d.symm : ℤ) =
        #(Ds.filter (fun e => e.snd = v)) := by
      rw [card_eq_sum_card_fiberwise (f := fun e => (m e).symm)
        (t := univ.filter (fun d : G.Dart => d.fst = v))]
      · push_cast
        refine sum_congr rfl fun d hd => ?_
        norm_cast
        change #(Ds.filter fun e => m e = _) = _
        congr 1
        ext e
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd ⊢
        constructor
        · rintro ⟨h1, h2⟩
          refine ⟨⟨h1, ?_⟩, by rw [h2, Dart.symm_symm]⟩
          rw [← hm_snd, ← hd, h2]
          rfl
        · rintro ⟨⟨h1, -⟩, h2⟩
          exact ⟨h1, by rw [← h2, Dart.symm_symm]⟩
      · intro e he
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at he ⊢
        exact he.2
    rw [e1, e2, hbal v]

end Jaeger
