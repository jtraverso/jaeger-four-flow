/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import SixFlowLib.SixFlowReduce

/-!
# From simple graphs to multigraphs and back

A finite simple graph is viewed as a multigraph whose edges are the darts going up with respect
to a fixed numbering of the vertices. A bridgeless graph has no 1-edge cuts, so the reduction
gives a nowhere-zero `ℤ₂ × ℤ₃`-flow, which becomes a nowhere-zero `ℤ/6`-flow on the darts by the
Chinese remainder theorem.
-/

@[expose] public section

open Finset SimpleGraph

attribute [local instance low] Classical.propDecidable

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace SixFlow

namespace Convert

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The multigraph of upward darts. -/
noncomputable def mg : MG V G.Dart :=
  ⟨univ.filter fun d : G.Dart => Fintype.equivFin V d.fst < Fintype.equivFin V d.snd,
    fun d => d.fst, fun d => d.snd⟩

variable {G}

lemma mem_act {d : G.Dart} :
    d ∈ (mg G).act ↔ Fintype.equivFin V d.fst < Fintype.equivFin V d.snd := by
  simp [mg]

lemma symm_mem_act {d : G.Dart} : d.symm ∈ (mg G).act ↔ d ∉ (mg G).act := by
  rw [mem_act, mem_act]
  simp only [Dart.symm_toProd, Prod.fst_swap, Prod.snd_swap, not_lt]
  have hne : Fintype.equivFin V d.fst ≠ Fintype.equivFin V d.snd :=
    fun h => d.adj.ne ((Fintype.equivFin V).injective h)
  constructor
  · exact le_of_lt
  · exact fun h => lt_of_le_of_ne h (Ne.symm hne)

lemma src_mg (d : G.Dart) : (mg G).src d = d.fst := rfl

lemma tgt_mg (d : G.Dart) : (mg G).tgt d = d.snd := rfl

/-- A bridgeless graph has no 1-edge cuts. -/
lemma cut_ne_one (hG : ∀ e ∈ G.edgeSet, ¬ G.IsBridge e) (S : Finset V) :
    ((mg G).cut S).card ≠ 1 := by
  intro h1
  obtain ⟨d, hd⟩ := card_eq_one.mp h1
  have hdC : d ∈ (mg G).cut S := by rw [hd]; exact mem_singleton_self d
  have hcr := (MG.mem_cut.mp hdC).2
  rw [src_mg, tgt_mg] at hcr
  have hnb := hG d.edge d.edge_mem
  rw [Dart.edge, Sym2.mk, ← Sym2.mk, isBridge_iff, not_not] at hnb
  -- a dart of `G - d.edge` leaving `S`
  obtain ⟨x, y, hxS, hyS, hxy⟩ : ∃ x y, x ∈ S ∧ y ∉ S ∧
      (G.deleteEdges {s(d.fst, d.snd)}).Reachable x y := by
    rcases hcr with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨_, _, h1, h2, hnb⟩
    · exact ⟨_, _, h2, h1, hnb.symm⟩
  obtain ⟨p⟩ := hxy
  obtain ⟨d', -, hd1, hd2⟩ := p.exists_boundary_dart (↑S) (by simpa using hxS) (by simpa using hyS)
  have hadj := d'.adj
  rw [deleteEdges_adj] at hadj
  obtain ⟨hG', hne⟩ := hadj
  set D : G.Dart := ⟨d'.toProd, hG'⟩ with hD
  have hDe : D.edge ≠ d.edge := by
    intro h
    apply hne
    rw [Set.mem_singleton_iff]
    exact h
  have key : ∀ D' : G.Dart, D'.edge = D.edge → D' ∈ (mg G).act → D' ∈ (mg G).cut S → False := by
    intro D' hD' _ hC
    rw [hd, mem_singleton] at hC
    exact hDe (by rw [← hC]; exact hD'.symm)
  by_cases hDa : D ∈ (mg G).act
  · refine key D rfl hDa (MG.mem_cut.mpr ⟨hDa, Or.inl ?_⟩)
    rw [src_mg, tgt_mg]
    exact ⟨by simpa using hd1, by simpa using hd2⟩
  · have hDs : D.symm ∈ (mg G).act := symm_mem_act.mpr hDa
    refine key D.symm (Dart.edge_symm D) hDs (MG.mem_cut.mpr ⟨hDs, Or.inr ?_⟩)
    rw [src_mg, tgt_mg]
    exact ⟨by simpa using hd2, by simpa using hd1⟩

/-- A multigraph flow on the upward darts gives an antisymmetric flow on all darts. -/
lemma dart_flow {A : Type*} [AddCommGroup A] (f : G.Dart → A) (hf : (mg G).bd f = 0)
    (hn : ∀ d ∈ (mg G).act, f d ≠ 0) :
    ∃ φ : G.Dart → A, (∀ d, φ d.symm = -φ d) ∧ (∀ d, φ d ≠ 0) ∧
      ∀ v, ∑ d ∈ univ.filter (fun d : G.Dart ↦ d.fst = v), φ d = 0 := by
  set φ : G.Dart → A := fun d => if d ∈ (mg G).act then f d else -f d.symm with hφ
  refine ⟨φ, fun d => ?_, fun d => ?_, fun v => ?_⟩
  · by_cases hd : d ∈ (mg G).act
    · have : d.symm ∉ (mg G).act := fun h => symm_mem_act.mp h hd
      simp [hφ, hd, this]
    · have : d.symm ∈ (mg G).act := symm_mem_act.mpr hd
      simp [hφ, hd, this]
  · by_cases hd : d ∈ (mg G).act
    · simp only [hφ, hd, if_true]
      exact hn d hd
    · simp only [hφ, hd, if_false, neg_ne_zero]
      exact hn _ (symm_mem_act.mpr hd)
  · have hbd : (∑ d ∈ (mg G).act, if d.snd = v then f d else 0) -
        (∑ d ∈ (mg G).act, if d.fst = v then f d else 0) = 0 := by
      have := congrFun hf v
      simp only [MG.bd, Pi.zero_apply] at this
      rw [← sum_sub_distrib]
      refine Eq.trans (sum_congr rfl fun x _ => ?_) this
      rw [src_mg, tgt_mg]
      congr 1 <;> split_ifs <;> first | rfl | contradiction
    have h1 : ∑ d ∈ univ.filter (fun d : G.Dart ↦ d.fst = v), φ d =
        ∑ d, ((if d.fst = v then (if d ∈ (mg G).act then f d else 0) else 0) +
          (if d.fst = v then (if d ∈ (mg G).act then 0 else -f d.symm) else 0)) := by
      rw [sum_filter]
      refine sum_congr rfl fun d _ => ?_
      by_cases h1 : d.fst = v <;> by_cases h2 : d ∈ (mg G).act <;> simp [hφ, h1, h2]
    have h2 : ∑ d : G.Dart, (if d.fst = v then (if d ∈ (mg G).act then f d else 0) else 0) =
        ∑ d ∈ (mg G).act, (if d.fst = v then f d else 0) := by
      rw [← sum_filter_add_sum_filter_not univ (· ∈ (mg G).act)]
      rw [sum_eq_zero (s := univ.filter fun d => d ∉ (mg G).act) (fun d hd => by
        simp [(mem_filter.mp hd).2]), add_zero]
      rw [filter_mem_eq_inter, univ_inter]
      exact sum_congr rfl fun d hd => by simp [hd]
    have h3 : ∑ d : G.Dart, (if d.fst = v then (if d ∈ (mg G).act then 0 else -f d.symm) else 0) =
        ∑ d ∈ (mg G).act, (if d.snd = v then -f d else 0) := by
      rw [← Fintype.sum_equiv (Dart.symm_involutive.toPerm _)
        (fun d : G.Dart => if d.snd = v then (if d ∈ (mg G).act then -f d else 0) else 0) _
        (fun d => by
          simp only [Function.Involutive.coe_toPerm, Dart.symm_toProd, Prod.fst_swap,
            symm_mem_act, Dart.symm_symm]
          by_cases h1 : d.snd = v <;> by_cases h2 : d ∈ (mg G).act <;> simp [h1, h2])]
      rw [← sum_filter_add_sum_filter_not univ (· ∈ (mg G).act)]
      rw [sum_eq_zero (s := univ.filter fun d => d ∉ (mg G).act) (fun d hd => by
        simp [(mem_filter.mp hd).2]), add_zero]
      rw [filter_mem_eq_inter, univ_inter]
      exact sum_congr rfl fun d hd => by simp [hd]
    rw [h1, sum_add_distrib, h2, h3]
    have h4 : ∑ d ∈ (mg G).act, (if d.snd = v then -f d else 0) =
        -∑ d ∈ (mg G).act, (if d.snd = v then f d else 0) := by
      rw [← sum_neg_distrib]
      exact sum_congr rfl fun d _ => by split_ifs <;> simp
    rw [h4, ← sub_eq_add_neg, ← neg_sub, hbd, neg_zero]

/-- Every finite bridgeless graph has a nowhere-zero `ℤ/6`-flow. -/
theorem exists_zmod6_flow (hG : ∀ e ∈ G.edgeSet, ¬ G.IsBridge e) :
    ∃ φ : G.Dart → ZMod (2 * 3), (∀ d, φ d.symm = -φ d) ∧ (∀ d, φ d ≠ 0) ∧
      ∀ v, ∑ d ∈ univ.filter (fun d : G.Dart ↦ d.fst = v), φ d = 0 := by
  obtain ⟨f, hf, hn⟩ := MG.reduce _ (mg G) rfl (cut_ne_one hG)
  obtain ⟨φ, ha, hnz, hc⟩ := dart_flow f hf hn
  set e := (ZMod.chineseRemainder (by norm_num : Nat.Coprime 2 3)).symm with he
  refine ⟨fun d => e (φ d), fun d => by simp only [ha, map_neg], fun d => ?_, fun v => ?_⟩
  · intro h0
    exact hnz d (e.injective (h0.trans (map_zero e).symm))
  · rw [← map_sum, hc v, map_zero]

end Convert

end SixFlow
