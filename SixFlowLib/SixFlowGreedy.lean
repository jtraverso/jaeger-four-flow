/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import SixFlowLib.SixFlowClaimB

/-!
# The greedy construction for 3-edge-connected multigraphs

We grow a vertex set `U` together with an even edge set `F ⊆ ins U` such that every
`ℤ₃`-demand on `U` is the boundary of a function supported on `ins U` that is nonzero outside
`F`. A new piece is attached to `U` through two edges, using closed trails (`claimB`) inside a
minimal leaf piece of the complement.
-/

@[expose] public section

open Finset SimpleGraph

attribute [local instance low] Classical.propDecidable

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace SixFlow

namespace MG

variable {V E : Type*} [Fintype V] {M : MG V E}

/-- Every `ℤ₃`-demand on `U` with total zero is the boundary of a function supported on `ins U`
which is nonzero on `ins U \ F`. -/
def Z3 (M : MG V E) (U : Finset V) (F : Finset E) : Prop :=
  ∀ b : V → ZMod 3, (∀ v, v ∉ U → b v = 0) → ∑ v, b v = 0 →
    ∃ h : E → ZMod 3, (∀ e, e ∉ M.ins U → h e = 0) ∧ M.bd h = b ∧
      ∀ e ∈ M.ins U, e ∉ F → h e ≠ 0

lemma Conn.z3 {Q : Finset E} {W : Finset V} (hC : M.Conn Q W) : M.Z3 W Q := by
  intro b hb hsum
  set h0 : E → ZMod 3 := ind (M.ins W \ Q) 1 with hh0
  have hs0 : ∀ e, e ∉ M.ins W → h0 e = 0 := fun e he => by
    simp [hh0, ind, mem_sdiff, he]
  obtain ⟨h1, hs1, hbd1⟩ := hC.route (b - M.bd h0)
    (fun v hv => by simp [hb v hv, bd_eq_zero_of_supp hs0 hv])
    (by simp only [Pi.sub_apply]; rw [sum_sub_distrib, hsum, sum_bd, sub_zero])
  refine ⟨h0 + h1, fun e he => ?_, ?_, fun e he heQ => ?_⟩
  · have : e ∉ Q := fun h => he (hC.1 h)
    simp [hs0 e he, hs1 e this]
  · rw [bd_add, hbd1]
    abel
  · simp only [Pi.add_apply, hs1 e heQ, add_zero, hh0, ind, mem_sdiff, he, heQ, not_false_eq_true,
      and_self, ite_true]
    decide

lemma sum_split {A : Type*} [AddCommGroup A] {U W : Finset V} {g : V → A}
    (hg : ∀ v, v ∉ U ∪ W → g v = 0) (hd : Disjoint U W) :
    ∑ v, g v = ∑ v ∈ U, g v + ∑ v ∈ W, g v := by
  rw [← sum_union hd]
  exact (sum_subset (subset_univ _) (fun v _ hv => hg v hv)).symm

lemma sum_ite_univ {A : Type*} [AddCommGroup A] (U : Finset V) (g : V → A) :
    ∑ v, (if v ∈ U then g v else 0) = ∑ v ∈ U, g v := by
  rw [sum_ite_mem, univ_inter]

/-- An edge joining `U` and `W`. -/
def Joins (M : MG V E) (U W : Finset V) (e : E) : Prop :=
  e ∈ M.act ∧ ((M.src e ∈ U ∧ M.tgt e ∈ W) ∨ (M.src e ∈ W ∧ M.tgt e ∈ U))

lemma sum_bd_ind_joins {U W : Finset V} (hd : Disjoint U W) {e : E} (he : M.Joins U W e) :
    ∃ p : Bool, ∀ a : ZMod 3, ∑ v ∈ U, M.bd (ind {e} a) v = if p then a else -a := by
  refine ⟨decide (M.tgt e ∈ U), fun a => ?_⟩
  rw [sum_congr rfl fun v _ => bd_ind_single he.1 a v, sum_sub_distrib, sum_ite_eq, sum_ite_eq]
  rcases he.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have : M.tgt e ∉ U := disjoint_right.mp hd h2
    simp [h1, this]
  · have : M.src e ∉ U := disjoint_right.mp hd h1
    simp [h2, this]

lemma joins_mem_ins {U W : Finset V} {e : E} (he : M.Joins U W e) : e ∈ M.ins (U ∪ W) := by
  rcases he.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact mem_ins.mpr ⟨he.1, mem_union_left _ h1, mem_union_right _ h2⟩
  · exact mem_ins.mpr ⟨he.1, mem_union_right _ h1, mem_union_left _ h2⟩

lemma joins_not_ins_left {U W : Finset V} (hd : Disjoint U W) {e : E} (he : M.Joins U W e) :
    e ∉ M.ins U := by
  intro h
  have h' := mem_ins.mp h
  rcases he.2 with ⟨-, h2⟩ | ⟨h1, -⟩
  · exact disjoint_left.mp hd h'.2.2 h2
  · exact disjoint_left.mp hd h'.2.1 h1

lemma joins_not_ins_right {U W : Finset V} (hd : Disjoint U W) {e : E} (he : M.Joins U W e) :
    e ∉ M.ins W := by
  intro h
  have h' := mem_ins.mp h
  rcases he.2 with ⟨h1, -⟩ | ⟨-, h2⟩
  · exact disjoint_left.mp hd h1 h'.2.1
  · exact disjoint_left.mp hd h2 h'.2.2

lemma zmod3_choice : ∀ (τ : ZMod 3) (p q : Bool), ∃ α β : ZMod 3, α ≠ 0 ∧ β ≠ 0 ∧
    (if p then α else -α) + (if q then β else -β) = τ := by decide

/-- **Merging** two pieces joined by two distinct edges. -/
lemma z3_merge {U W : Finset V} {F Q : Finset E} (hU : M.Z3 U F) (hW : M.Z3 W Q)
    (hd : Disjoint U W) {e1 e2 : E} (hne : e1 ≠ e2) (h1 : M.Joins U W e1)
    (h2 : M.Joins U W e2) : M.Z3 (U ∪ W) (F ∪ Q) := by
  intro b hb hsum
  set C := M.ins (U ∪ W) \ (M.ins U ∪ M.ins W) with hC
  set hc0 : E → ZMod 3 := fun e => if e ∈ C ∧ e ≠ e1 ∧ e ≠ e2 then 1 else 0 with hhc0
  obtain ⟨p, hp⟩ := sum_bd_ind_joins hd h1
  obtain ⟨q, hq⟩ := sum_bd_ind_joins hd h2
  obtain ⟨α, β, hα, hβ, hαβ⟩ :=
    zmod3_choice (∑ v ∈ U, b v - ∑ v ∈ U, M.bd hc0 v) p q
  set hcr : E → ZMod 3 := hc0 + ind {e1} α + ind {e2} β with hhcr
  have hcrU : ∑ v ∈ U, M.bd hcr v = ∑ v ∈ U, b v := by
    rw [hhcr, bd_add, bd_add]
    simp only [Pi.add_apply, sum_add_distrib, hp, hq]
    rw [add_assoc, hαβ]
    abel
  have hcr_supp : ∀ e, e ∉ M.ins (U ∪ W) → hcr e = 0 := by
    intro e he
    have hC' : e ∉ C := fun h => he (mem_sdiff.mp h).1
    have h1' : e ≠ e1 := fun h => he (h ▸ joins_mem_ins h1)
    have h2' : e ≠ e2 := fun h => he (h ▸ joins_mem_ins h2)
    simp [hhcr, hhc0, ind, hC', h1', h2']
  have hbdcr : ∀ v, v ∉ U ∪ W → M.bd hcr v = 0 := fun v hv => bd_eq_zero_of_supp hcr_supp hv
  set bU : V → ZMod 3 := fun v => if v ∈ U then b v - M.bd hcr v else 0 with hbU
  set bW : V → ZMod 3 := fun v => if v ∈ W then b v - M.bd hcr v else 0 with hbW
  have hsumU : ∑ v, bU v = 0 := by
    rw [hbU, sum_ite_univ, sum_sub_distrib, hcrU, sub_self]
  have hsumW : ∑ v, bW v = 0 := by
    rw [hbW, sum_ite_univ, sum_sub_distrib]
    have e1' := sum_split hb hd
    have e2' := sum_split hbdcr hd
    rw [hsum] at e1'
    rw [sum_bd] at e2'
    rw [hcrU] at e2'
    have : ∑ v ∈ W, b v = ∑ v ∈ W, M.bd hcr v := by
      have := e1'.symm.trans e2'
      exact add_left_cancel this
    rw [this, sub_self]
  obtain ⟨g1, hs1, hbd1, hn1⟩ := hU bU (fun v hv => by simp [hbU, hv]) hsumU
  obtain ⟨g2, hs2, hbd2, hn2⟩ := hW bW (fun v hv => by simp [hbW, hv]) hsumW
  refine ⟨g1 + g2 + hcr, fun e he => ?_, ?_, fun e he heFQ => ?_⟩
  · have a1 : e ∉ M.ins U := fun h => he (ins_mono subset_union_left h)
    have a2 : e ∉ M.ins W := fun h => he (ins_mono subset_union_right h)
    simp [hs1 e a1, hs2 e a2, hcr_supp e he]
  · rw [bd_add, bd_add, hbd1, hbd2]
    funext v
    simp only [Pi.add_apply, hbU, hbW]
    by_cases hvU : v ∈ U
    · have hvW : v ∉ W := disjoint_left.mp hd hvU
      simp [hvU, hvW]
    · by_cases hvW : v ∈ W
      · simp [hvU, hvW]
      · have hv : v ∉ U ∪ W := by simp [hvU, hvW]
        simp [hvU, hvW, hbdcr v hv, hb v hv]
  · rw [mem_union, not_or] at heFQ
    have hx1 : e1 ∉ M.ins U := joins_not_ins_left hd h1
    have hx2 : e2 ∉ M.ins U := joins_not_ins_left hd h2
    have hy1 : e1 ∉ M.ins W := joins_not_ins_right hd h1
    have hy2 : e2 ∉ M.ins W := joins_not_ins_right hd h2
    by_cases heU : e ∈ M.ins U
    · have a2 : e ∉ M.ins W := by
        intro h
        exact disjoint_left.mp hd (mem_ins.mp heU).2.1 (mem_ins.mp h).2.1
      have b1 : e ≠ e1 := fun h => hx1 (h ▸ heU)
      have b2 : e ≠ e2 := fun h => hx2 (h ▸ heU)
      have hC' : e ∉ C := fun h => (mem_sdiff.mp h).2 (mem_union_left _ heU)
      simpa [hs2 e a2, hhcr, hhc0, ind, hC', b1, b2] using hn1 e heU heFQ.1
    by_cases heW : e ∈ M.ins W
    · have b1 : e ≠ e1 := fun h => hy1 (h ▸ heW)
      have b2 : e ≠ e2 := fun h => hy2 (h ▸ heW)
      have hC' : e ∉ C := fun h => (mem_sdiff.mp h).2 (mem_union_right _ heW)
      simpa [hs1 e heU, hhcr, hhc0, ind, hC', b1, b2] using hn2 e heW heFQ.2
    have hC' : e ∈ C := mem_sdiff.mpr ⟨he, by simp [heU, heW]⟩
    simp only [Pi.add_apply, hs1 e heU, hs2 e heW, zero_add, hhcr, hhc0, ind, mem_singleton]
    by_cases b1 : e = e1
    · subst b1
      simp [hne, hα]
    · by_cases b2 : e = e2
      · subst b2
        simp [b1, hβ]
      · simp [b1, b2, hC']

/-! ### Leaf pieces -/

/-- Edges leaving `S` towards vertices outside `U`. -/
noncomputable def outU (M : MG V E) (U S : Finset V) : Finset E :=
  (M.cut S).filter fun e => M.src e ∉ U ∧ M.tgt e ∉ U

/-- Edges leaving `S` towards `U`. -/
noncomputable def attU (M : MG V E) (U S : Finset V) : Finset E :=
  (M.cut S).filter fun e => M.src e ∈ U ∨ M.tgt e ∈ U

lemma cut_subset_att_out (U S : Finset V) : M.cut S ⊆ M.attU U S ∪ M.outU U S := by
  intro e he
  simp only [attU, outU, mem_union, mem_filter]
  by_cases h : M.src e ∈ U ∨ M.tgt e ∈ U
  · exact Or.inl ⟨he, h⟩
  · push_neg at h
    exact Or.inr ⟨he, h⟩

lemma card_cut_le (U S : Finset V) : (M.cut S).card ≤ (M.attU U S).card + (M.outU U S).card :=
  (card_le_card (cut_subset_att_out U S)).trans (card_union_le _ _)

lemma outU_subset {U R S : Finset V} (hRS : R ⊆ S) :
    M.outU U R ⊆ (M.outU U S ∩ M.cut R) ∪ (M.ins S ∩ M.cut R) := by
  intro e he
  simp only [outU, mem_filter] at he
  obtain ⟨hcut, hU⟩ := he
  have hc := mem_cut.mp hcut
  by_cases hS : M.src e ∈ S ∧ M.tgt e ∈ S
  · exact mem_union_right _ (mem_inter.mpr ⟨mem_ins.mpr ⟨hc.1, hS⟩, hcut⟩)
  · refine mem_union_left _ (mem_inter.mpr ⟨?_, hcut⟩)
    simp only [outU, mem_filter]
    refine ⟨mem_cut.mpr ⟨hc.1, ?_⟩, hU⟩
    rcases hc.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨hRS h1, fun h => hS ⟨hRS h1, h⟩⟩
    · exact Or.inr ⟨fun h => hS ⟨h, hRS h2⟩, hRS h2⟩

lemma attU_subset {U C S : Finset V} (hCS : C ⊆ S) (hSU : Disjoint S U) :
    M.attU U S ⊆ M.attU U C ∪ M.attU U (S \ C) := by
  intro e he
  simp only [attU, mem_filter, mem_union, mem_cut, mem_sdiff] at he ⊢
  obtain ⟨⟨hA, hc⟩, hU⟩ := he
  have h1 : M.src e ∈ U → M.src e ∉ S := fun h h' => disjoint_left.mp hSU h' h
  have h2 : M.tgt e ∈ U → M.tgt e ∉ S := fun h h' => disjoint_left.mp hSU h' h
  have h3 : M.src e ∈ C → M.src e ∈ S := fun h => hCS h
  have h4 : M.tgt e ∈ C → M.tgt e ∈ S := fun h => hCS h
  tauto

lemma ins_cut_sdiff {R S : Finset V} (hRS : R ⊆ S) :
    M.ins S ∩ M.cut (S \ R) = M.ins S ∩ M.cut R := by
  ext e
  simp only [mem_inter, mem_ins, mem_cut, mem_sdiff]
  have h1 : M.src e ∈ R → M.src e ∈ S := fun h => hRS h
  have h2 : M.tgt e ∈ R → M.tgt e ∈ S := fun h => hRS h
  tauto

/-- **Leaf pieces.** If edges leave `U`, then there is a connected even subgraph outside `U`
attached to `U` by two distinct edges. -/
lemma leaf_piece (h12 : ∀ S, (M.cut S).card ≠ 1 ∧ (M.cut S).card ≠ 2) {U : Finset V}
    (hcut : (M.cut U).Nonempty) :
    ∃ W Q e1 e2, Disjoint U W ∧ M.Conn Q W ∧ M.Ev Q ∧ e1 ≠ e2 ∧ M.Joins U W e1 ∧
      M.Joins U W e2 := by
  set cands := (univ : Finset (Finset V)).filter fun S => S.Nonempty ∧ Disjoint S U ∧
    (M.outU U S).card ≤ 1 ∧ (M.attU U S).Nonempty with hcands
  have hUc : Uᶜ ∈ cands := by
    obtain ⟨e, he⟩ := hcut
    have hc := mem_cut.mp he
    have heUc : e ∈ M.cut Uᶜ := by
      refine mem_cut.mpr ⟨hc.1, ?_⟩
      simp only [mem_compl]
      tauto
    refine mem_filter.mpr ⟨mem_univ _, ?_, disjoint_compl_left, ?_, ⟨e, ?_⟩⟩
    · rcases hc.2 with ⟨-, h⟩ | ⟨h, -⟩
      · exact ⟨_, mem_compl.mpr h⟩
      · exact ⟨_, mem_compl.mpr h⟩
    · have : M.outU U Uᶜ = ∅ := by
        ext f
        simp only [outU, mem_filter, mem_cut, mem_compl, notMem_empty, iff_false]
        tauto
      rw [this, card_empty]
      exact zero_le_one
    · simp only [attU, mem_filter]
      exact ⟨heUc, by tauto⟩
  obtain ⟨S, hS, hmin⟩ := exists_min_image cands card ⟨_, hUc⟩
  obtain ⟨-, hSne, hSU, hout, hatt⟩ := mem_filter.mp hS
  have hsmall : ∀ R ⊆ S, R.Nonempty → R.card < S.card → (M.outU U R).card ≤ 1 →
      M.attU U R = ∅ := by
    intro R hRS hRne hlt hRout
    by_contra hne
    have := hmin R (mem_filter.mpr ⟨mem_univ _, hRne, disjoint_of_subset_left hRS hSU, hRout,
      nonempty_iff_ne_empty.mpr hne⟩)
    omega
  -- connectivity
  have hconn : ∀ a ∈ S, ∀ b ∈ S, (M.shadow (M.ins S)).Reachable a b := by
    intro a ha b hb
    by_contra hab
    set C := S.filter fun c => (M.shadow (M.ins S)).Reachable a c with hC
    have hCS : C ⊆ S := filter_subset _ _
    have haC : a ∈ C := mem_filter.mpr ⟨ha, Reachable.refl _⟩
    have hbC : b ∉ C := fun h => hab (mem_filter.mp h).2
    have hclosed : M.ins S ∩ M.cut C = ∅ := by
      ext e
      simp only [mem_inter, notMem_empty, iff_false, not_and]
      intro heS hec
      have hS' := mem_ins.mp heS
      have hc := (mem_cut.mp hec).2
      have key : ∀ c d, c ∈ C → d ∈ S → d ∉ C → s(M.src e, M.tgt e) = s(c, d) → False := by
        intro c d hc hd hd' hsym
        have hcd : c ≠ d := fun h => hd' (h ▸ hc)
        have hadj : (M.shadow (M.ins S)).Adj c d := shadow_adj.mpr ⟨⟨e, heS, hsym⟩, hcd⟩
        exact hd' (mem_filter.mpr ⟨hd, (mem_filter.mp hc).2.trans hadj.reachable⟩)
      rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact key _ _ h1 hS'.2.2 h2 rfl
      · exact key _ _ h2 hS'.2.1 h1 Sym2.eq_swap
    have hout' : ∀ R ⊆ S, M.ins S ∩ M.cut R = ∅ → (M.outU U R).card ≤ 1 := by
      intro R hRS hR
      refine (card_le_card ((outU_subset hRS).trans ?_)).trans hout
      rw [hR, union_empty]
      exact inter_subset_left
    have hA1 := hsmall C hCS ⟨a, haC⟩ (card_lt_card ⟨hCS, fun h => hbC (h hb)⟩) (hout' C hCS hclosed)
    have hDS : S \ C ⊆ S := sdiff_subset
    have hA2 := hsmall (S \ C) hDS ⟨b, mem_sdiff.mpr ⟨hb, hbC⟩⟩
      (card_lt_card ⟨hDS, fun h => (mem_sdiff.mp (h ha)).2 haC⟩)
      (hout' _ hDS (by rw [ins_cut_sdiff hCS, hclosed]))
    have := attU_subset hCS hSU (M := M)
    rw [hA1, hA2, union_empty] at this
    obtain ⟨f, hf⟩ := hatt
    exact notMem_empty f (this hf)
  -- no bridges inside `S`
  have h2 : ∀ T ⊆ S, (M.ins S ∩ M.cut T).card ≠ 1 := by
    intro T hTS hT1
    obtain ⟨e, he⟩ := card_eq_one.mp hT1
    have heT : e ∈ M.ins S ∩ M.cut T := by rw [he]; exact mem_singleton_self e
    have key : ∀ R ⊆ S, R.Nonempty → R.card < S.card → M.ins S ∩ M.cut R = {e} →
        M.outU U S ∩ M.cut R = ∅ → False := by
      intro R hRS hRne hlt hR hO
      have hRout : M.outU U R ⊆ {e} := by
        have := outU_subset hRS (M := M) (U := U)
        rwa [hO, hR, empty_union] at this
      have hA := hsmall R hRS hRne hlt ((card_le_card hRout).trans (card_singleton e).le)
      have hcR := card_cut_le U R (M := M)
      rw [hA, card_empty, zero_add] at hcR
      have heR : e ∈ M.cut R := by
        have : e ∈ M.ins S ∩ M.cut R := by rw [hR]; exact mem_singleton_self e
        exact (mem_inter.mp this).2
      have h1 : 0 < (M.cut R).card := card_pos.mpr ⟨e, heR⟩
      have h3 := card_le_card hRout
      rw [card_singleton] at h3
      exact (h12 R).1 (by omega)
    obtain ⟨heS, hec⟩ := mem_inter.mp heT
    have hS' := mem_ins.mp heS
    have hc := (mem_cut.mp hec).2
    have hTne : T.Nonempty := by
      rcases hc with ⟨h, -⟩ | ⟨-, h⟩
      · exact ⟨_, h⟩
      · exact ⟨_, h⟩
    have hDne : (S \ T).Nonempty := by
      rcases hc with ⟨-, h⟩ | ⟨h, -⟩
      · exact ⟨_, mem_sdiff.mpr ⟨hS'.2.2, h⟩⟩
      · exact ⟨_, mem_sdiff.mpr ⟨hS'.2.1, h⟩⟩
    have hTlt : T.card < S.card := by
      obtain ⟨d, hd⟩ := hDne
      exact card_lt_card ⟨hTS, fun h => (mem_sdiff.mp hd).2 (h (mem_sdiff.mp hd).1)⟩
    have hDlt : (S \ T).card < S.card := by
      obtain ⟨t, ht⟩ := hTne
      exact card_lt_card ⟨sdiff_subset, fun h => (mem_sdiff.mp (h (hTS ht))).2 ht⟩
    have hdisj : Disjoint (M.outU U S ∩ M.cut T) (M.outU U S ∩ M.cut (S \ T)) := by
      refine disjoint_left.mpr fun f hf1 hf2 => ?_
      simp only [outU, mem_inter, mem_filter, mem_cut, mem_sdiff] at hf1 hf2
      have a1 : M.src f ∈ T → M.src f ∈ S := fun h => hTS h
      have a2 : M.tgt f ∈ T → M.tgt f ∈ S := fun h => hTS h
      tauto
    have hcard : (M.outU U S ∩ M.cut T).card + (M.outU U S ∩ M.cut (S \ T)).card ≤ 1 := by
      rw [← card_union_of_disjoint hdisj]
      exact (card_le_card (union_subset inter_subset_left inter_subset_left)).trans hout
    by_cases hO : M.outU U S ∩ M.cut T = ∅
    · exact key T hTS hTne hTlt he hO
    · have hO2 : M.outU U S ∩ M.cut (S \ T) = ∅ := by
        rw [← card_eq_zero]
        have := card_pos.mpr (nonempty_iff_ne_empty.mpr hO)
        omega
      exact key (S \ T) sdiff_subset hDne hDlt (by rw [ins_cut_sdiff hTS, he]) hO2
  -- two attachment edges
  have hatt2 : 1 < (M.attU U S).card := by
    have h0 : (M.cut S).card ≠ 0 := by
      obtain ⟨f, hf⟩ := hatt
      exact (card_pos.mpr ⟨f, (mem_filter.mp hf).1⟩).ne'
    have := card_cut_le U S (M := M)
    have := (h12 S).1
    have := (h12 S).2
    omega
  obtain ⟨e1, he1, e2, he2, hne⟩ := one_lt_card.mp hatt2
  have endpt : ∀ e ∈ M.attU U S, ∃ x ∈ S, ∀ W, x ∈ W → M.Joins U W e := by
    intro e he
    simp only [attU, mem_filter, mem_cut] at he
    obtain ⟨⟨hA, hc⟩, hU⟩ := he
    rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have : M.tgt e ∈ U := by
        rcases hU with h | h
        · exact absurd h1 (disjoint_right.mp hSU h)
        · exact h
      exact ⟨_, h1, fun W hW => ⟨hA, Or.inr ⟨hW, this⟩⟩⟩
    · have : M.src e ∈ U := by
        rcases hU with h | h
        · exact h
        · exact absurd h2 (disjoint_right.mp hSU h)
      exact ⟨_, h2, fun W hW => ⟨hA, Or.inl ⟨this, hW⟩⟩⟩
  obtain ⟨x1, hx1, hj1⟩ := endpt e1 he1
  obtain ⟨x2, hx2, hj2⟩ := endpt e2 he2
  obtain ⟨Q, W, -, hWS, hx1W, hx2W, hC, hE⟩ := claimB hconn h2 hx1 hx2
  exact ⟨W, Q, e1, e2, (disjoint_of_subset_left hWS hSU).symm, hC, hE, hne, hj1 W hx1W,
    hj2 W hx2W⟩

lemma bd_prod {A B : Type*} [AddCommGroup A] [AddCommGroup B] (g : E → A) (h : E → B) (v : V) :
    M.bd (fun e => (g e, h e)) v = (M.bd g v, M.bd h v) := by
  ext <;> simp [bd, Prod.fst_sum, Prod.snd_sum, apply_ite Prod.fst, apply_ite Prod.snd]

/-- **The greedy construction.** A connected multigraph in which every edge cut has at least
three edges has a nowhere-zero `ℤ₂ × ℤ₃`-flow. -/
theorem greedy (h12 : ∀ S, (M.cut S).card ≠ 1 ∧ (M.cut S).card ≠ 2)
    (h0 : ∀ S, M.cut S = ∅ → M.ins S = ∅ ∨ M.ins Sᶜ = ∅) {e0 : E} (he0 : e0 ∈ M.act) :
    ∃ f : E → ZMod 2 × ZMod 3, M.bd f = 0 ∧ ∀ e ∈ M.act, f e ≠ 0 := by
  have main : ∀ n, ∀ U : Finset V, ∀ F : Finset E, Uᶜ.card = n → M.src e0 ∈ U →
      F ⊆ M.ins U → M.Ev F → M.Z3 U F →
      ∃ f : E → ZMod 2 × ZMod 3, M.bd f = 0 ∧ ∀ e ∈ M.act, f e ≠ 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro U F hn hv0 hFU hEF hZ
    by_cases hc : (M.cut U).Nonempty
    · obtain ⟨W, Q, e1, e2, hd, hC, hEQ, hne, hj1, hj2⟩ := leaf_piece h12 hc
      have hWne : W.Nonempty := by
        rcases hj1.2 with ⟨-, h⟩ | ⟨h, -⟩
        · exact ⟨_, h⟩
        · exact ⟨_, h⟩
      obtain ⟨w, hw⟩ := hWne
      have hlt : (U ∪ W)ᶜ.card < Uᶜ.card := by
        refine card_lt_card ⟨compl_subset_compl.mpr subset_union_left, fun h => ?_⟩
        have hwU : w ∈ Uᶜ := mem_compl.mpr (disjoint_right.mp hd hw)
        exact mem_compl.mp (h hwU) (mem_union_right _ hw)
      have hFQ : Disjoint F Q := by
        refine disjoint_left.mpr fun e heF heQ => ?_
        exact disjoint_left.mp hd (mem_ins.mp (hFU heF)).2.1 (mem_ins.mp (hC.1 heQ)).2.1
      exact ih _ (hn ▸ hlt) (U ∪ W) (F ∪ Q) rfl (mem_union_left _ hv0)
        (union_subset (hFU.trans (ins_mono subset_union_left))
          (hC.1.trans (ins_mono subset_union_right)))
        (hEF.union hEQ hFQ) (z3_merge hZ hC.z3 hd hne hj1 hj2)
    · rw [not_nonempty_iff_eq_empty] at hc
      have he0U : e0 ∈ M.ins U := by
        have : e0 ∉ M.cut U := by rw [hc]; exact notMem_empty _
        rw [mem_cut] at this
        refine mem_ins.mpr ⟨he0, hv0, ?_⟩
        by_contra h
        exact this ⟨he0, Or.inl ⟨hv0, h⟩⟩
      have hins : M.ins Uᶜ = ∅ := by
        rcases h0 U hc with h | h
        · rw [h] at he0U
          exact absurd he0U (notMem_empty _)
        · exact h
      have hall : ∀ e ∈ M.act, e ∈ M.ins U := by
        intro e he
        have h1 : e ∉ M.cut U := by rw [hc]; exact notMem_empty _
        have h2 : e ∉ M.ins Uᶜ := by rw [hins]; exact notMem_empty _
        rw [mem_cut] at h1
        rw [mem_ins] at h2 ⊢
        simp only [mem_compl] at h2
        refine ⟨he, ?_⟩
        tauto
      obtain ⟨h, -, hbd, hnz⟩ := hZ 0 (fun _ _ => rfl) (by simp)
      refine ⟨fun e => (ind F (1 : ZMod 2) e, h e), ?_, fun e he => ?_⟩
      · funext v
        rw [bd_prod, hbd]
        have : M.bd (ind F (1 : ZMod 2)) v = 0 := by rw [hEF]; rfl
        rw [this]
        rfl
      · by_cases heF : e ∈ F
        · intro h'
          have := congrArg Prod.fst h'
          simp [ind, heF] at this
        · intro h'
          have := congrArg Prod.snd h'
          exact hnz e (hall e he) heF this
  exact main _ {M.src e0} ∅ rfl (mem_singleton_self _) (empty_subset _) Ev.empty
    (Conn.singleton_empty _).z3

end MG

end SixFlow
