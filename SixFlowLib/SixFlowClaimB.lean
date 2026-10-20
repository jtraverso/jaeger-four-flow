/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import SixFlowLib.SixFlowMG

/-!
# Connected even subgraphs through two vertices

In a connected multigraph without bridges, any two vertices lie in a common connected even
subgraph (a closed trail). This is proved by growing a connected even subgraph along ears.
-/

@[expose] public section

open Finset SimpleGraph

attribute [local instance low] Classical.propDecidable

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace SixFlow

namespace MG

variable {V E : Type*} [Fintype V] {M : MG V E}

/-- The `ℤ₂`-demand with ones at `u` and `u'`. -/
noncomputable def dd (u u' : V) : V → ZMod 2 :=
  fun v => (if v = u then 1 else 0) + (if v = u' then 1 else 0)

lemma bd_ind_single2 {e : E} (he : e ∈ M.act) :
    M.bd (ind {e} (1 : ZMod 2)) = dd (M.src e) (M.tgt e) := by
  funext v
  rw [bd_ind_single he, zmod2_sub, dd, add_comm]
  simp only [eq_comm]

lemma dd_self (u : V) : dd u u = 0 := by
  funext v
  simp only [dd, Pi.zero_apply]
  exact zmod2_add_self _

lemma dd_comm (u u' : V) : dd u u' = dd u' u := by
  funext v
  simp only [dd]
  exact add_comm _ _

lemma dd_add (a b c : V) : dd a b + dd b c = dd a c := by
  funext v
  simp only [dd, Pi.add_apply]
  split_ifs <;> rfl

lemma reachable_shadow_of_walk {Q Q' : Finset E} {a b : V} (p : (M.shadow Q).Walk a b)
    (P : V → Prop) (ha : P a) (hP : ∀ e ∈ Q, P (M.src e) ∨ P (M.tgt e) → e ∈ Q' ∧
      P (M.src e) ∧ P (M.tgt e)) : (M.shadow Q').Reachable a b := by
  induction p with
  | nil => rfl
  | @cons a c b hadj p ih =>
    rw [shadow_adj] at hadj
    obtain ⟨⟨e, he, he'⟩, hne⟩ := hadj
    have hends : (M.src e = a ∧ M.tgt e = c) ∨ (M.src e = c ∧ M.tgt e = a) := by
      rcases Sym2.eq_iff.mp he' with h | h
      · exact Or.inl h
      · exact Or.inr h
    have key := hP e he (by rcases hends with ⟨h, -⟩ | ⟨-, h⟩ <;> simp [h, ha])
    have hc : P c := by rcases hends with ⟨-, h⟩ | ⟨h, -⟩ <;> rw [← h] <;> simp [key]
    exact (Adj.reachable (shadow_adj.mpr ⟨⟨e, key.1, he'⟩, hne⟩)).trans (ih hc)

/-- **Splitting a connected even subgraph** at two of its vertices into two connected parts,
each with odd degree exactly at these two vertices. -/
lemma split {Q₀ : Finset E} {W₀ : Finset V} (hE : M.Ev Q₀) (hC : M.Conn Q₀ W₀) {u u' : V}
    (hu : u ∈ W₀) (hu' : u' ∈ W₀) (huu : u ≠ u') :
    ∃ A B KA KB, A ⊆ Q₀ ∧ B ⊆ Q₀ ∧ M.Conn A KA ∧ M.Conn B KB ∧ u ∈ KA ∧ u' ∈ KA ∧
      u ∈ KB ∧ u' ∈ KB ∧ KA ⊆ W₀ ∧ KB ⊆ W₀ ∧ W₀ ⊆ KA ∪ KB ∧
      M.bd (ind A (1 : ZMod 2)) = dd u u' ∧ M.bd (ind B (1 : ZMod 2)) = dd u u' := by
  have hQA : Q₀ ⊆ M.act := hC.1.trans (ins_subset W₀)
  obtain ⟨p⟩ := hC.2 u hu u' hu'
  obtain ⟨R, WR, hRQ, -, huR, hu'R, hCR, hbdR⟩ := path_edges hQA p.toPath.1 p.toPath.2
  set D := Q₀ \ R with hD
  have hbdD : M.bd (ind D (1 : ZMod 2)) = dd u u' := by
    rw [hD, ind_sdiff hRQ, bd_sub, hE, hbdR, zero_sub]
    funext v
    simp only [Pi.neg_apply, zmod2_neg]
    rfl
  set KA : Finset V := univ.filter fun v => (M.shadow D).Reachable u v with hKA
  have mKA : ∀ v, v ∈ KA ↔ (M.shadow D).Reachable u v := fun v => by simp [hKA]
  have fA : ∀ e ∈ D, (M.src e ∈ KA ↔ M.tgt e ∈ KA) := by
    intro e he
    have := reachable_of_mem (M := M) he
    rw [mKA, mKA]
    exact ⟨fun h => h.trans this, fun h => h.trans this.symm⟩
  set A := D.filter fun e => M.src e ∈ KA with hA
  have mA : ∀ e, e ∈ A ↔ e ∈ D ∧ M.src e ∈ KA := fun e => by simp [hA]
  have huK : u ∈ KA := (mKA u).mpr (Reachable.refl _)
  have hDQ : D ⊆ Q₀ := sdiff_subset
  have hbdA : ∀ v, M.bd (ind A (1 : ZMod 2)) v = if v ∈ KA then M.bd (ind D 1) v else 0 := by
    intro v
    split_ifs with hv
    · refine sum_congr rfl fun e _ => ?_
      by_cases ht : M.tgt e = v
      · by_cases heD : e ∈ D
        · have : e ∈ A := (mA e).mpr ⟨heD, (fA e heD).mpr (ht ▸ hv)⟩
          simp [ind, this, heD]
        · have : e ∉ A := fun h => heD ((mA e).mp h).1
          simp [ind, this, heD]
      · by_cases hs : M.src e = v
        · by_cases heD : e ∈ D
          · have : e ∈ A := (mA e).mpr ⟨heD, hs ▸ hv⟩
            simp [ind, this, heD]
          · have : e ∉ A := fun h => heD ((mA e).mp h).1
            simp [ind, this, heD]
        · simp [ht, hs]
    · refine sum_eq_zero fun e _ => ?_
      by_cases heA : e ∈ A
      · obtain ⟨heD, hsK⟩ := (mA e).mp heA
        have htK := (fA e heD).mp hsK
        have h1 : M.tgt e ≠ v := fun h => hv (h ▸ htK)
        have h2 : M.src e ≠ v := fun h => hv (h ▸ hsK)
        simp [h1, h2]
      · simp [ind, heA]
  have hu'K : u' ∈ KA := by
    by_contra hu'K
    have h1 : ∑ v ∈ KA, M.bd (ind A (1 : ZMod 2)) v = 0 := by
      rw [← sum_bd (M := M) (ind A (1 : ZMod 2))]
      exact sum_subset (subset_univ _) fun v _ hv => by rw [hbdA v, if_neg hv]
    rw [sum_congr rfl fun v hv => by rw [hbdA v, if_pos hv, hbdD]] at h1
    rw [show ∑ v ∈ KA, dd u u' v = ∑ v ∈ KA, ((if v = u then (1 : ZMod 2) else 0) +
      (if v = u' then 1 else 0)) from rfl, sum_add_distrib, sum_ite_eq', sum_ite_eq',
      if_pos huK, if_neg hu'K, add_zero] at h1
    exact one_ne_zero h1
  have hbdA' : M.bd (ind A (1 : ZMod 2)) = dd u u' := by
    funext v
    rw [hbdA v]
    split_ifs with hv
    · rw [hbdD]
    · have h1 : v ≠ u := fun h => hv (h ▸ huK)
      have h2 : v ≠ u' := fun h => hv (h ▸ hu'K)
      simp [dd, h1, h2]
  have hAK : A ⊆ M.ins KA := by
    intro e he
    obtain ⟨heD, hsK⟩ := (mA e).mp he
    exact mem_ins.mpr ⟨hQA (hDQ heD), hsK, (fA e heD).mp hsK⟩
  have hreachA : ∀ v ∈ KA, (M.shadow A).Reachable u v := by
    intro v hv
    obtain ⟨q⟩ := (mKA v).mp hv
    refine reachable_shadow_of_walk q (· ∈ KA) huK fun e he h => ?_
    have : M.src e ∈ KA := by
      rcases h with h | h
      · exact h
      · exact (fA e he).mpr h
    exact ⟨(mA e).mpr ⟨he, this⟩, this, (fA e he).mp this⟩
  have hCA : M.Conn A KA :=
    ⟨hAK, fun a ha b hb => (hreachA a ha).symm.trans (hreachA b hb)⟩
  set B := Q₀ \ A with hB
  have hAQ : A ⊆ Q₀ := fun e he => hDQ ((mA e).mp he).1
  have hbdB : M.bd (ind B (1 : ZMod 2)) = dd u u' := by
    rw [hB, ind_sdiff hAQ, bd_sub, hE, hbdA', zero_sub]
    funext v
    simp only [Pi.neg_apply, zmod2_neg]
  have hRB : R ⊆ B := by
    intro e he
    rw [hB, mem_sdiff]
    refine ⟨hRQ he, fun h => ?_⟩
    have := ((mA e).mp h).1
    rw [hD, mem_sdiff] at this
    exact this.2 he
  set KB : Finset V := univ.filter fun v => (M.shadow B).Reachable u v with hKB
  have mKB : ∀ v, v ∈ KB ↔ (M.shadow B).Reachable u v := fun v => by simp [hKB]
  have hWRK : WR ⊆ KB := fun v hv =>
    (mKB v).mpr ((hCR.2 u huR v hv).mono (shadow_mono hRB))
  have hBQ : B ⊆ Q₀ := sdiff_subset
  have hKAW : KA ⊆ W₀ := fun v hv =>
    mem_of_reachable (hDQ.trans hC.1) hu ((mKA v).mp hv)
  have hKBW : KB ⊆ W₀ := fun v hv =>
    mem_of_reachable (hBQ.trans hC.1) hu ((mKB v).mp hv)
  have hcover : W₀ ⊆ KA ∪ KB := by
    intro v hv
    by_contra hvY
    obtain ⟨q⟩ := hC.2 u hu v hv
    obtain ⟨d, -, hd1, hd2⟩ := q.exists_boundary_dart (↑(KA ∪ KB) : Set V)
      (by simp [huK]) (by simpa using hvY)
    simp only [coe_union, Set.mem_union, mem_coe] at hd1 hd2
    have hadj := d.adj
    rw [shadow_adj] at hadj
    obtain ⟨⟨e, he, he'⟩, hne⟩ := hadj
    have hends : (M.src e = d.fst ∧ M.tgt e = d.snd) ∨ (M.src e = d.snd ∧ M.tgt e = d.fst) := by
      rcases Sym2.eq_iff.mp he' with h | h
      · exact Or.inl h
      · exact Or.inr h
    by_cases heA : e ∈ A
    · have h1 := (mA e).mp heA
      have h2 := (fA e h1.1).mp h1.2
      apply hd2
      left
      rcases hends with ⟨-, h⟩ | ⟨h, -⟩
      · exact h ▸ h2
      · exact h ▸ h1.2
    have heB : e ∈ B := by rw [hB, mem_sdiff]; exact ⟨he, heA⟩
    by_cases hfB : d.fst ∈ KB
    · apply hd2
      right
      rw [mKB] at hfB ⊢
      exact hfB.trans (Adj.reachable (shadow_adj.mpr ⟨⟨e, heB, he'⟩, hne⟩))
    have hfA : d.fst ∈ KA := by tauto
    by_cases heR : e ∈ R
    · have := mem_ins.mp (hCR.1 heR)
      apply hfB
      apply hWRK
      rcases hends with ⟨h, -⟩ | ⟨-, h⟩
      · exact h ▸ this.2.1
      · exact h ▸ this.2.2
    · have heD : e ∈ D := by rw [hD, mem_sdiff]; exact ⟨he, heR⟩
      apply heA
      refine (mA e).mpr ⟨heD, ?_⟩
      rcases hends with ⟨h, -⟩ | ⟨-, h⟩
      · exact h ▸ hfA
      · exact (fA e heD).mpr (h ▸ hfA)
  have hBK : B ⊆ M.ins KB := by
    intro e he
    by_cases heR : e ∈ R
    · have := mem_ins.mp (hCR.1 heR)
      exact mem_ins.mpr ⟨hQA (hBQ he), hWRK this.2.1, hWRK this.2.2⟩
    · rw [hB, mem_sdiff] at he
      have heD : e ∈ D := by rw [hD, mem_sdiff]; exact ⟨he.1, heR⟩
      have hsA : M.src e ∉ KA := fun h => he.2 ((mA e).mpr ⟨heD, h⟩)
      have htA : M.tgt e ∉ KA := fun h => hsA ((fA e heD).mpr h)
      have hW := mem_ins.mp (hC.1 he.1)
      have hs := hcover hW.2.1
      have ht := hcover hW.2.2
      rw [mem_union] at hs ht
      exact mem_ins.mpr ⟨hW.1, hs.resolve_left hsA, ht.resolve_left htA⟩
  have hCB : M.Conn B KB :=
    ⟨hBK, fun a ha b hb => ((mKB a).mp ha).symm.trans ((mKB b).mp hb)⟩
  exact ⟨A, B, KA, KB, hAQ, hBQ, hCA, hCB, huK, hu'K, (mKB u).mpr (Reachable.refl _),
    hWRK hu'R, hKAW, hKBW, hcover, hbdA', hbdB⟩

/-- **Ear step.** A connected even subgraph inside a bridgeless piece `S` can be modified so
that it keeps a given vertex `x` and contains a new neighbour `w`. -/
lemma ear_step {S : Finset V} (h2 : ∀ T ⊆ S, (M.ins S ∩ M.cut T).card ≠ 1)
    {Q₀ : Finset E} {W₀ : Finset V} (hQS : Q₀ ⊆ M.ins S) (hWS : W₀ ⊆ S) (hC : M.Conn Q₀ W₀)
    (hE : M.Ev Q₀) {x w₀ w : V} (hx : x ∈ W₀) (hw₀ : w₀ ∈ W₀) (hwS : w ∈ S) (hw : w ∉ W₀)
    (hadj : (M.shadow (M.ins S)).Adj w₀ w) :
    ∃ Q₁ W₁, Q₁ ⊆ M.ins S ∧ W₁ ⊆ S ∧ x ∈ W₁ ∧ w ∈ W₁ ∧ M.Conn Q₁ W₁ ∧ M.Ev Q₁ := by
  rw [shadow_adj] at hadj
  obtain ⟨⟨e, heS, he'⟩, -⟩ := hadj
  have heA : e ∈ M.act := ins_subset S heS
  set T₀ := S \ W₀ with hT₀
  have hwT : w ∈ T₀ := mem_sdiff.mpr ⟨hwS, hw⟩
  set Z : Finset V := univ.filter fun z => (M.shadow (M.ins T₀)).Reachable w z with hZ
  have mZ : ∀ z, z ∈ Z ↔ (M.shadow (M.ins T₀)).Reachable w z := fun z => by simp [hZ]
  have hZT : Z ⊆ T₀ := fun z hz => mem_of_reachable subset_rfl hwT ((mZ z).mp hz)
  have hZS : Z ⊆ S := hZT.trans sdiff_subset
  have hwZ : w ∈ Z := (mZ w).mpr (Reachable.refl _)
  have hw₀Z : w₀ ∉ Z := fun h => (mem_sdiff.mp (hZT h)).2 hw₀
  have hends : (M.src e = w₀ ∧ M.tgt e = w) ∨ (M.src e = w ∧ M.tgt e = w₀) := by
    rcases Sym2.eq_iff.mp he' with h | h
    · exact Or.inl h
    · exact Or.inr h
  have heC : e ∈ M.ins S ∩ M.cut Z := by
    refine mem_inter.mpr ⟨heS, mem_cut.mpr ⟨heA, ?_⟩⟩
    rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · right; rw [h1, h2]; exact ⟨hw₀Z, hwZ⟩
    · left; rw [h1, h2]; exact ⟨hwZ, hw₀Z⟩
  have hcard : 1 < (M.ins S ∩ M.cut Z).card := by
    have h0 : 0 < (M.ins S ∩ M.cut Z).card := card_pos.mpr ⟨e, heC⟩
    have := h2 Z hZS
    omega
  obtain ⟨e', he'C, hne'⟩ := exists_mem_ne hcard e
  obtain ⟨he'S, he'cut⟩ := mem_inter.mp he'C
  obtain ⟨he'A, hcr⟩ := mem_cut.mp he'cut
  obtain ⟨z', o, hz', ho, hends'⟩ : ∃ z' o, z' ∈ Z ∧ o ∉ Z ∧
      ((M.src e' = z' ∧ M.tgt e' = o) ∨ (M.src e' = o ∧ M.tgt e' = z')) := by
    rcases hcr with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨_, _, h1, h2, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨_, _, h2, h1, Or.inr ⟨rfl, rfl⟩⟩
  have he'S' := mem_ins.mp he'S
  have hoS : o ∈ S := by
    rcases hends' with ⟨-, h⟩ | ⟨h, -⟩
    · exact h ▸ he'S'.2.2
    · exact h ▸ he'S'.2.1
  have hz'T := hZT hz'
  have hz'W : z' ∉ W₀ := (mem_sdiff.mp hz'T).2
  have hoW : o ∈ W₀ := by
    by_contra hoW
    have hoT : o ∈ T₀ := mem_sdiff.mpr ⟨hoS, hoW⟩
    have he'T : e' ∈ M.ins T₀ := by
      rcases hends' with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact mem_ins.mpr ⟨he'A, h1 ▸ hz'T, h2 ▸ hoT⟩
      · exact mem_ins.mpr ⟨he'A, h1 ▸ hoT, h2 ▸ hz'T⟩
    have hzo : z' ≠ o := fun h => ho (h ▸ hz')
    have hadj' : (M.shadow (M.ins T₀)).Adj z' o := by
      refine shadow_adj.mpr ⟨⟨e', he'T, ?_⟩, hzo⟩
      rcases hends' with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
      exact Sym2.eq_swap
    exact ho ((mZ o).mpr (((mZ z').mp hz').trans hadj'.reachable))
  obtain ⟨q⟩ := (mZ z').mp hz'
  obtain ⟨P₀, WP, hP₀, hWPsupp, hwWP, hz'WP, hCP, hbdP⟩ :=
    path_edges (ins_subset T₀) q.toPath.1 q.toPath.2
  have hWPT : WP ⊆ T₀ := fun v hv =>
    support_subset_of_ins subset_rfl hwT q.toPath.1 v (by simpa using hWPsupp hv)
  have hoT : o ∉ T₀ := fun h => (mem_sdiff.mp h).2 hoW
  have he'P : e' ∉ P₀ := by
    intro h
    have := mem_ins.mp (hP₀ h)
    rcases hends' with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact hoT (h2 ▸ this.2.2)
    · exact hoT (h1 ▸ this.2.1)
  have hw₀T : w₀ ∉ T₀ := fun h => (mem_sdiff.mp h).2 hw₀
  have heP : e ∉ ({e'} ∪ P₀ : Finset E) := by
    rw [mem_union, mem_singleton, not_or]
    refine ⟨hne'.symm, fun h => ?_⟩
    have := mem_ins.mp (hP₀ h)
    rcases hends with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact hw₀T (h1 ▸ this.2.1)
    · exact hw₀T (h2 ▸ this.2.2)
  set ear : Finset E := {e} ∪ ({e'} ∪ P₀) with hear
  set Wear : Finset V := ({M.src e, M.tgt e} : Finset V) ∪
    (({M.src e', M.tgt e'} : Finset V) ∪ WP) with hWear
  have hz'e : z' ∈ ({M.src e', M.tgt e'} : Finset V) := by
    rcases hends' with ⟨h1, -⟩ | ⟨-, h2⟩
    · simp [h1]
    · simp [h2]
  have hwe : w ∈ ({M.src e, M.tgt e} : Finset V) := by
    rcases hends with ⟨-, h2⟩ | ⟨h1, -⟩
    · simp [h2]
    · simp [h1]
  have hCear : M.Conn ear Wear :=
    (Conn.single heA).union ((Conn.single he'A).union hCP hz'e hz'WP) hwe
      (mem_union_right _ hwWP)
  have hw₀e : w₀ ∈ Wear := by
    rcases hends with ⟨h1, -⟩ | ⟨-, h2⟩
    · simp [hWear, h1]
    · simp [hWear, h2]
  have hoe : o ∈ Wear := by
    rcases hends' with ⟨-, h2⟩ | ⟨h1, -⟩
    · simp [hWear, h2]
    · simp [hWear, h1]
  have hwWear : w ∈ Wear := mem_union_left _ hwe
  have hWearS : Wear ⊆ S := by
    intro v hv
    simp only [hWear, mem_union, mem_insert, mem_singleton] at hv
    rcases hv with (rfl | rfl) | (rfl | rfl) | hv
    · exact (mem_ins.mp heS).2.1
    · exact (mem_ins.mp heS).2.2
    · exact he'S'.2.1
    · exact he'S'.2.2
    · exact (mem_sdiff.mp (hWPT hv)).1
  have hearS : ear ⊆ M.ins S := by
    intro f hf
    simp only [hear, mem_union, mem_singleton] at hf
    rcases hf with rfl | rfl | hf
    · exact heS
    · exact he'S
    · exact ins_mono sdiff_subset (hP₀ hf)
  have hbdear : M.bd (ind ear (1 : ZMod 2)) = dd w₀ o := by
    rw [hear, ind_union (disjoint_singleton_left.mpr heP),
      ind_union (disjoint_singleton_left.mpr he'P), bd_add, bd_add, bd_ind_single2 heA,
      bd_ind_single2 he'A, hbdP]
    have h1 : dd (M.src e) (M.tgt e) = dd w₀ w := by
      rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
      exact dd_comm _ _
    have h2' : dd (M.src e') (M.tgt e') = dd z' o := by
      rcases hends' with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
      exact dd_comm _ _
    rw [h1, h2', show (fun v => (if v = w then (1 : ZMod 2) else 0) + if v = z' then 1 else 0)
      = dd w z' from rfl, ← add_assoc, add_right_comm, dd_add, dd_add]
  have hdisj : ∀ A ⊆ Q₀, Disjoint A ear := by
    intro A hA
    refine disjoint_left.mpr fun f hfA hf => ?_
    have hfW := mem_ins.mp (hC.1 (hA hfA))
    simp only [hear, mem_union, mem_singleton] at hf
    rcases hf with rfl | rfl | hf
    · rcases hends with ⟨-, h2⟩ | ⟨h1, -⟩
      · exact hw (h2 ▸ hfW.2.2)
      · exact hw (h1 ▸ hfW.2.1)
    · rcases hends' with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact hz'W (h1 ▸ hfW.2.1)
      · exact hz'W (h2 ▸ hfW.2.2)
    · exact (mem_sdiff.mp (mem_ins.mp (hP₀ hf)).2.1).2 hfW.2.1
  by_cases hwo : w₀ = o
  · refine ⟨Q₀ ∪ ear, W₀ ∪ Wear, union_subset hQS hearS, union_subset hWS hWearS,
      mem_union_left _ hx, mem_union_right _ hwWear, hC.union hCear hw₀ hw₀e, ?_⟩
    refine hE.union ?_ (hdisj Q₀ subset_rfl)
    unfold Ev
    rw [hbdear, hwo, dd_self]
  · obtain ⟨A, B, KA, KB, hAQ, hBQ, hCA, hCB, hw₀A, hoA, hw₀B, hoB, hKA, hKB, hcov, hbdA,
      hbdB⟩ := split hE hC hw₀ hoW hwo
    rcases mem_union.mp (hcov hx) with hxA | hxB
    · refine ⟨A ∪ ear, KA ∪ Wear, union_subset (hAQ.trans hQS) hearS,
        union_subset (hKA.trans hWS) hWearS, mem_union_left _ hxA, mem_union_right _ hwWear,
        hCA.union hCear hw₀A hw₀e, ?_⟩
      unfold Ev
      rw [ind_union (hdisj A hAQ), bd_add, hbdA, hbdear]
      funext v
      exact zmod2_add_self _
    · refine ⟨B ∪ ear, KB ∪ Wear, union_subset (hBQ.trans hQS) hearS,
        union_subset (hKB.trans hWS) hWearS, mem_union_left _ hxB, mem_union_right _ hwWear,
        hCB.union hCear hw₀B hw₀e, ?_⟩
      unfold Ev
      rw [ind_union (hdisj B hBQ), bd_add, hbdB, hbdear]
      funext v
      exact zmod2_add_self _

/-- **Closed trails through two vertices.** In a connected bridgeless piece `S` of a multigraph,
any two vertices lie in a common connected even subgraph. -/
lemma claimB {S : Finset V} (hconn : ∀ a ∈ S, ∀ b ∈ S, (M.shadow (M.ins S)).Reachable a b)
    (h2 : ∀ T ⊆ S, (M.ins S ∩ M.cut T).card ≠ 1) {x y : V} (hx : x ∈ S) (hy : y ∈ S) :
    ∃ Q W, Q ⊆ M.ins S ∧ W ⊆ S ∧ x ∈ W ∧ y ∈ W ∧ M.Conn Q W ∧ M.Ev Q := by
  have main : ∀ n : ℕ, ∀ Q₀ W₀, Q₀ ⊆ M.ins S → W₀ ⊆ S → x ∈ W₀ → M.Conn Q₀ W₀ → M.Ev Q₀ →
      ∀ w₀ ∈ W₀, ∀ p : (M.shadow (M.ins S)).Walk w₀ y, p.length ≤ n →
      ∃ Q W, Q ⊆ M.ins S ∧ W ⊆ S ∧ x ∈ W ∧ y ∈ W ∧ M.Conn Q W ∧ M.Ev Q := by
    intro n
    induction n with
    | zero =>
      intro Q₀ W₀ hQ hW hx hC hE w₀ hw₀ p hp
      have := Walk.eq_of_length_eq_zero (Nat.le_zero.mp hp)
      subst this
      exact ⟨Q₀, W₀, hQ, hW, hx, hw₀, hC, hE⟩
    | succ n ih =>
      intro Q₀ W₀ hQ hW hx hC hE w₀ hw₀ p hp
      cases p with
      | nil => exact ⟨Q₀, W₀, hQ, hW, hx, hw₀, hC, hE⟩
      | @cons _ w _ hadj p' =>
        rw [Walk.length_cons] at hp
        have hwS : w ∈ S := mem_of_reachable subset_rfl (hW hw₀) hadj.reachable
        by_cases hw : w ∈ W₀
        · exact ih Q₀ W₀ hQ hW hx hC hE w hw p' (by omega)
        · obtain ⟨Q₁, W₁, hQ₁, hW₁, hx₁, hw₁, hC₁, hE₁⟩ :=
            ear_step h2 hQ hW hC hE hx hw₀ hwS hw hadj
          exact ih Q₁ W₁ hQ₁ hW₁ hx₁ hC₁ hE₁ w hw₁ p' (by omega)
  obtain ⟨p⟩ := hconn x hx y hy
  exact main p.length ∅ {x} (empty_subset _) (singleton_subset_iff.mpr hx) (mem_singleton_self x)
    (Conn.singleton_empty x) Ev.empty x (mem_singleton_self x) p le_rfl

end MG

end SixFlow
