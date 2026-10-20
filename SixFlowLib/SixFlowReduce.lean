/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import SixFlowLib.SixFlowGreedy

/-!
# Reduction to the 3-edge-connected case

By induction on the number of edges, a multigraph without 1-edge cuts has a nowhere-zero
`ℤ₂ × ℤ₃`-flow: we split along empty cuts, contract an edge of a 2-edge cut, and otherwise
apply the greedy construction.
-/

@[expose] public section

open Finset SimpleGraph

attribute [local instance low] Classical.propDecidable

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace SixFlow

namespace MG

variable {V E : Type*} [Fintype V]

/-- The same multigraph with another set of active edges. -/
def withAct (M : MG V E) (F : Finset E) : MG V E := ⟨F, M.src, M.tgt⟩

@[simp] lemma withAct_act (M : MG V E) (F : Finset E) : (M.withAct F).act = F := rfl
@[simp] lemma withAct_src (M : MG V E) (F : Finset E) : (M.withAct F).src = M.src := rfl
@[simp] lemma withAct_tgt (M : MG V E) (F : Finset E) : (M.withAct F).tgt = M.tgt := rfl

lemma cut_withAct_ins {M : MG V E} {S : Finset V} (hS : M.cut S = ∅) (T : Finset V) :
    (M.withAct (M.ins S)).cut T = M.cut (T ∩ S) := by
  ext e
  have h : e ∉ M.cut S := by rw [hS]; exact notMem_empty e
  rw [mem_cut] at h
  rw [mem_cut, mem_cut, withAct_act, mem_ins, withAct_src, withAct_tgt]
  simp only [mem_inter]
  tauto

lemma cut_compl (M : MG V E) (S : Finset V) : M.cut Sᶜ = M.cut S := by
  ext e
  simp only [cut, mem_filter, mem_compl]
  tauto

lemma bd_withAct_split {A : Type*} [AddCommGroup A] {M : MG V E} {S : Finset V}
    (hS : M.cut S = ∅) (f1 f2 : E → A) :
    M.bd (fun e => if e ∈ M.ins S then f1 e else f2 e) =
      (M.withAct (M.ins S)).bd f1 + (M.withAct (M.ins Sᶜ)).bd f2 := by
  have hact : M.act = M.ins S ∪ M.ins Sᶜ := by
    ext e
    have h : e ∉ M.cut S := by rw [hS]; exact notMem_empty e
    simp only [cut, ins, mem_filter, mem_union, mem_compl] at h ⊢
    tauto
  have hd : Disjoint (M.ins S) (M.ins Sᶜ) := by
    refine disjoint_left.mpr fun e h1 h2 => ?_
    exact (mem_compl.mp (mem_ins.mp h2).2.1) (mem_ins.mp h1).2.1
  funext v
  simp only [bd, withAct, Pi.add_apply]
  rw [hact, sum_union hd]
  congr 1
  · exact sum_congr rfl fun e he => by simp [he]
  · refine sum_congr rfl fun e he => ?_
    have : e ∉ M.ins S := fun h => disjoint_left.mp hd h he
    simp [this]

/-- Contraction of the edge `e`: its head is identified with its tail. -/
noncomputable def contr (M : MG V E) (e : E) : MG V E :=
  ⟨M.act.erase e, fun x => if M.src x = M.tgt e then M.src e else M.src x,
    fun x => if M.tgt x = M.tgt e then M.src e else M.tgt x⟩

/-- **Reduction.** Every multigraph without 1-edge cuts has a nowhere-zero `ℤ₂ × ℤ₃`-flow. -/
theorem reduce : ∀ n, ∀ M : MG V E, M.act.card = n → (∀ S, (M.cut S).card ≠ 1) →
    ∃ f : E → ZMod 2 × ZMod 3, M.bd f = 0 ∧ ∀ e ∈ M.act, f e ≠ 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro M hn h1
  rcases M.act.eq_empty_or_nonempty with h0 | ⟨e0, he0⟩
  · exact ⟨0, bd_zero, fun e he => by rw [h0] at he; exact absurd he (notMem_empty e)⟩
  by_cases hA : ∃ S, M.cut S = ∅ ∧ (M.ins S).Nonempty ∧ (M.ins Sᶜ).Nonempty
  · obtain ⟨S, hS, hne1, hne2⟩ := hA
    have hSc : M.cut Sᶜ = ∅ := by rw [cut_compl, hS]
    have hd : Disjoint (M.ins S) (M.ins Sᶜ) := by
      refine disjoint_left.mpr fun e h1 h2 => ?_
      exact (mem_compl.mp (mem_ins.mp h2).2.1) (mem_ins.mp h1).2.1
    have hlt : ∀ (T : Finset V), (M.ins T).Nonempty → (M.ins Tᶜ).Nonempty →
        (M.ins T).card < M.act.card := by
      intro T _ hT2
      obtain ⟨x, hx⟩ := hT2
      refine card_lt_card ⟨ins_subset T, fun h => ?_⟩
      have := mem_ins.mp (h (ins_subset _ hx))
      exact (mem_compl.mp (mem_ins.mp hx).2.1) this.2.1
    obtain ⟨f1, hf1, hn1⟩ := ih _ (hn ▸ hlt S hne1 hne2) (M.withAct (M.ins S)) rfl
      (fun T => by rw [cut_withAct_ins hS]; exact h1 _)
    obtain ⟨f2, hf2, hn2⟩ := ih _ (hn ▸ hlt Sᶜ hne2 (by rwa [compl_compl])) (M.withAct (M.ins Sᶜ))
      rfl (fun T => by rw [cut_withAct_ins hSc]; exact h1 _)
    refine ⟨fun e => if e ∈ M.ins S then f1 e else f2 e, ?_, fun e he => ?_⟩
    · rw [bd_withAct_split hS, hf1, hf2, add_zero]
    · by_cases h : e ∈ M.ins S
      · simp only [h, if_true]
        exact hn1 e h
      · simp only [h, if_false]
        refine hn2 e ?_
        have hc : e ∉ M.cut S := by rw [hS]; exact notMem_empty e
        rw [mem_cut] at hc
        rw [mem_ins] at h
        rw [withAct_act, mem_ins]
        simp only [mem_compl]
        tauto
  by_cases hB : ∃ S, (M.cut S).card = 2
  · obtain ⟨S, hS⟩ := hB
    obtain ⟨e, g, heg, hcut⟩ := card_eq_two.mp hS
    have heC : e ∈ M.cut S := by rw [hcut]; simp
    have hgC : g ∈ M.cut S := by rw [hcut]; simp
    have heA : e ∈ M.act := (mem_cut.mp heC).1
    have hgA : g ∈ M.act := (mem_cut.mp hgC).1
    have hab : M.src e ≠ M.tgt e := by
      intro h
      rcases (mem_cut.mp heC).2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h] at h1
        exact h2 h1
      · rw [h] at h1
        exact h1 h2
    set a := M.src e with ha
    set b := M.tgt e with hb
    set π : V → V := fun v => if v = b then a else v with hπ
    have hπv : ∀ x v, v ≠ a → v ≠ b → (π x = v ↔ x = v) := by
      intro x v hva hvb
      simp only [hπ]
      split_ifs with h
      · subst h
        exact ⟨fun h' => absurd h'.symm hva, fun h' => absurd h'.symm hvb⟩
      · exact Iff.rfl
    set M' := M.contr e with hM'
    have hsrc : ∀ x, M'.src x = π (M.src x) := fun x => rfl
    have htgt : ∀ x, M'.tgt x = π (M.tgt x) := fun x => rfl
    have hcut' : ∀ T, M'.cut T = M.cut (univ.filter fun v => π v ∈ T) := by
      intro T
      ext x
      simp only [cut, mem_filter, mem_univ, true_and, hsrc, htgt]
      simp only [hM', contr, mem_erase]
      constructor
      · rintro ⟨⟨-, hx⟩, hc⟩
        exact ⟨hx, hc⟩
      · rintro ⟨hx, hc⟩
        refine ⟨⟨?_, hx⟩, hc⟩
        rintro rfl
        have : π (M.src x) = π (M.tgt x) := by
          simp only [hπ, ← ha, ← hb, if_pos rfl]
          rw [if_neg hab]
        rw [this] at hc
        tauto
    obtain ⟨f', hf', hn'⟩ := ih _ (hn ▸ card_erase_lt_of_mem heA) M' (card_erase_of_mem heA ▸ rfl)
      (fun T => by rw [hcut']; exact h1 _)
    set f0 := Function.update f' e 0 with hf0
    set c := -M.bd f0 b with hc
    set f := f0 + ind {e} c with hf
    have hfe : f e = c := by simp [hf, hf0, ind]
    have hfx : ∀ x, x ≠ e → f x = f' x := by
      intro x hx
      simp [hf, hf0, ind, hx]
    have hclaim : ∀ v, v ≠ a → v ≠ b → M.bd f0 v = M'.bd f' v := by
      intro v hva hvb
      simp only [bd]
      rw [← add_sum_erase _ _ heA]
      have h0 : f0 e = 0 := by simp [hf0]
      rw [h0]
      simp only [ite_self, sub_self, zero_add]
      simp only [hM', contr]
      refine sum_congr rfl fun x hx => ?_
      have hxe : x ≠ e := ne_of_mem_erase hx
      have hf0x : f0 x = f' x := by simp [hf0, hxe]
      rw [hf0x]
      have e1 := hπv (M.tgt x) v hva hvb
      have e2 := hπv (M.src x) v hva hvb
      simp only [hπ] at e1 e2
      rw [show (if (if M.tgt x = M.tgt e then M.src e else M.tgt x) = v then f' x else 0) =
          (if M.tgt x = v then f' x else 0) from by simp only [← hb, ← ha]; exact if_congr e1 rfl rfl,
        show (if (if M.src x = M.tgt e then M.src e else M.src x) = v then f' x else 0) =
          (if M.src x = v then f' x else 0) from by simp only [← hb, ← ha]; exact if_congr e2 rfl rfl]
    have hbdf : M.bd f = 0 := by
      have hbd1 : ∀ v, v ≠ a → M.bd f v = 0 := by
        intro v hva
        rw [hf, bd_add, Pi.add_apply, bd_ind_single heA]
        by_cases hvb : v = b
        · subst hvb
          have hsb : M.src e ≠ M.tgt e := hab
          rw [if_pos rfl, if_neg hsb, hc]
          abel
        · rw [hclaim v hva hvb, hf', Pi.zero_apply, if_neg (fun h => hvb (hb ▸ h.symm)),
            if_neg (fun h => hva (ha ▸ h.symm))]
          abel
      funext v
      by_cases hva : v = a
      · subst hva
        have := sum_bd (M := M) f
        rw [sum_eq_single (M.src e) (fun w _ hw => hbd1 w hw) (fun h => absurd (mem_univ _) h)]
          at this
        exact this
      · exact hbd1 v hva
    refine ⟨f, hbdf, fun x hx => ?_⟩
    by_cases hxe : x = e
    · subst hxe
      rw [hfe]
      intro hc0
      have hsum := sum_bd_set_cut (M := M) f S
      rw [hbdf] at hsum
      simp only [Pi.zero_apply, sum_const_zero] at hsum
      rw [hcut, sum_pair heg, hfe, hc0] at hsum
      simp only [ite_self, sub_self, zero_add] at hsum
      have hgf : f g ≠ 0 := by
        rw [hfx g (Ne.symm heg)]
        exact hn' g (mem_erase.mpr ⟨Ne.symm heg, hgA⟩)
      rcases (mem_cut.mp hgC).2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · simp [h1, h2] at hsum
        first | exact hgf hsum | exact hgf hsum.symm
      · simp [h1, h2] at hsum
        first | exact hgf hsum | exact hgf hsum.symm
    · rw [hfx x hxe]
      exact hn' x (mem_erase.mpr ⟨hxe, hx⟩)
  · push_neg at hA hB
    refine greedy (fun S => ⟨h1 S, hB S⟩) (fun S hS => ?_) he0
    by_contra hne
    push_neg at hne
    exact (not_nonempty_iff_eq_empty.mpr (hA S hS hne.1)) hne.2

end MG

end SixFlow
