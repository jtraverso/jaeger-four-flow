/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import EightFlowLib.Contraction
public import EightFlowLib.BaseCase

/-!
# Every bridgeless graph has a nowhere-zero `ℤ₂³`-flow

Induction on the number of edges: either one of the reductions applies, or every cut
separating two edges is crossed by at least three edges.
-/

@[expose] public section

open Finset SimpleGraph

attribute [local instance low] Classical.propDecidable

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace EightFlow

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- A triangle `a b d` in which `a` and `b` have degree two. -/
lemma two_deg2 {a b d : V} (hab : G.Adj a b) (had : G.Adj a d) (hbd : G.Adj b d)
    (hNa : ∀ w, G.Adj a w → w = b ∨ w = d) (hNb : ∀ w, G.Adj b w → w = a ∨ w = d) :
    R0p G ∨ R1p G := by
  have hda : d ≠ a := had.ne.symm
  have hdb : d ≠ b := hbd.ne.symm
  set S : Finset V := (univ.erase a).erase b with hSdef
  by_cases hS : ∃ x y, G.Adj x y ∧ x ∈ S ∧ y ∈ S
  · right
    refine ⟨S, d, mem_rest.mpr ⟨hda, hdb⟩, fun x y hx hy hxy => ?_, hS,
      ⟨a, b, hab, fun h => (mem_rest.mp h.1).1 rfl⟩⟩
    rw [mem_rest] at hx hy
    by_cases hya : y = a
    · subst hya
      rcases hNa x hxy.symm with h | h
      · exact absurd h hx.2
      · exact h
    · have hyb : y = b := by tauto
      subst hyb
      rcases hNb x hxy.symm with h | h
      · exact absurd h hx.1
      · exact h
  · left
    push Not at hS
    have hout : ∀ x y, G.Adj x y → x ≠ a → x ≠ b → y = a ∨ y = b := by
      intro x y hxy hxa hxb
      have := hS x y hxy (mem_rest.mpr ⟨hxa, hxb⟩)
      rw [mem_rest] at this
      tauto
    intro v
    rw [← card_neighborFinset_eq_degree]
    by_cases hva : v = a
    · subst hva
      have : G.neighborFinset v = {b, d} := by
        ext w
        rw [mem_neighborFinset, mem_insert, mem_singleton]
        exact ⟨hNa w, by rintro (rfl | rfl) <;> assumption⟩
      rw [this, card_pair hdb.symm]
      exact even_two
    by_cases hvb : v = b
    · subst hvb
      have : G.neighborFinset v = {a, d} := by
        ext w
        rw [mem_neighborFinset, mem_insert, mem_singleton]
        exact ⟨hNb w, by rintro (rfl | rfl) <;> [exact hab.symm; exact hbd]⟩
      rw [this, card_pair hda.symm]
      exact even_two
    by_cases hvd : v = d
    · subst hvd
      have : G.neighborFinset v = {a, b} := by
        ext w
        rw [mem_neighborFinset, mem_insert, mem_singleton]
        exact ⟨fun h => hout v w h hva hvb, by
          rintro (rfl | rfl) <;> [exact had.symm; exact hbd.symm]⟩
      rw [this, card_pair hab.ne]
      exact even_two
    · have : G.neighborFinset v = ∅ := by
        ext w
        rw [mem_neighborFinset]
        simp only [notMem_empty, iff_false]
        intro h
        rcases hout v w h hva hvb with rfl | rfl
        · rcases hNa v h.symm with h' | h' <;> simp_all
        · rcases hNb v h.symm with h' | h' <;> simp_all
      rw [this, card_empty]
      exact Even.zero

/-- A cut with exactly two crossing pairs sharing their tail. -/
lemma cut_two_same_tail (S : Finset V) {a b d : V} (hX : X G S = {(a, b), (a, d)})
    (hbd : b ≠ d) : R0p G ∨ R1p G ∨ R2p G ∨ R3p G := by
  have habm : (a, b) ∈ X G S := by rw [hX]; simp
  have hadm : (a, d) ∈ X G S := by rw [hX]; simp
  rw [mem_X] at habm hadm
  obtain ⟨ha, hb, hab⟩ := habm
  obtain ⟨-, hd, had⟩ := hadm
  have hcross : ∀ x y, x ∈ S → y ∉ S → G.Adj x y → x = a ∧ (y = b ∨ y = d) := by
    intro x y hx hy hxy
    have : (x, y) ∈ X G S := mem_X.mpr ⟨hx, hy, hxy⟩
    rw [hX] at this
    simp only [mem_insert, mem_singleton, Prod.mk.injEq] at this
    tauto
  by_cases hS : ∃ x y, G.Adj x y ∧ x ∈ S ∧ y ∈ S
  · exact Or.inr (Or.inl ⟨S, a, ha, fun x y hx hy hxy => (hcross x y hx hy hxy).1, hS,
      ⟨a, b, hab, fun h => hb h.2⟩⟩)
  push Not at hS
  have hNa : ∀ w, G.Adj a w → w = b ∨ w = d := by
    intro w hw
    exact (hcross a w ha (hS a w hw ha) hw).2
  by_cases hbd' : G.Adj b d
  · by_cases hψ : ∃ ψ : V → V → ZMod 2, IsFl (isoA G a) ψ ∧ ψ b d ≠ 0
    · exact Or.inr (Or.inr (Or.inr ⟨a, b, d, hab, had, hbd', hNa, hψ⟩))
    obtain ⟨R, hbR, hdR, hR⟩ :=
      bridge_cut (G := isoA G a) ⟨hbd', hab.ne.symm, had.ne.symm⟩ hψ
    by_cases haR : a ∈ R
    · by_cases hR' : ∃ x y, G.Adj x y ∧ x ∈ Rᶜ ∧ y ∈ Rᶜ
      · refine Or.inr (Or.inl ⟨Rᶜ, d, mem_compl.mpr hdR, fun x y hx hy hxy => ?_, hR',
          ⟨a, b, hab, fun h => mem_compl.mp h.1 haR⟩⟩)
        rw [mem_compl] at hx
        rw [mem_compl, not_not] at hy
        have hxa : x ≠ a := fun h => hx (h ▸ haR)
        by_cases hya : y = a
        · subst hya
          rcases hNa x hxy.symm with rfl | rfl
          · exact absurd hbR hx
          · rfl
        · exact (hR y x hy hx ⟨hxy.symm, hya, hxa⟩).2
      · push Not at hR'
        have hNd : ∀ w, G.Adj d w → w = a ∨ w = b := by
          intro w hw
          by_cases hwR : w ∈ R
          · by_cases hwa : w = a
            · exact Or.inl hwa
            · exact Or.inr (hR w d hwR hdR ⟨hw.symm, hwa, had.ne.symm⟩).1
          · exact absurd (mem_compl.mpr hwR) (hR' d w hw (mem_compl.mpr hdR))
        rcases two_deg2 had hab hbd'.symm (fun w h => (hNa w h).symm) hNd with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
    · by_cases hR' : ∃ x y, G.Adj x y ∧ x ∈ R ∧ y ∈ R
      · refine Or.inr (Or.inl ⟨R, b, hbR, fun x y hx hy hxy => ?_, hR',
          ⟨a, b, hab, fun h => haR h.1⟩⟩)
        have hxa : x ≠ a := fun h => haR (h ▸ hx)
        by_cases hya : y = a
        · subst hya
          rcases hNa x hxy.symm with rfl | rfl
          · rfl
          · exact absurd hx hdR
        · exact (hR x y hx hy ⟨hxy, hxa, hya⟩).1
      · push Not at hR'
        have hNb : ∀ w, G.Adj b w → w = a ∨ w = d := by
          intro w hw
          by_cases hwR : w ∈ R
          · exact absurd hwR (hR' b w hw hbR)
          · by_cases hwa : w = a
            · exact Or.inl hwa
            · exact Or.inr (hR b w hbR hwR ⟨hw, hab.ne.symm, hwa⟩).2
        rcases two_deg2 hab had hbd' hNa hNb with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
  · refine Or.inr (Or.inr (Or.inl ⟨a, b, hab, fun w ⟨h1, h2⟩ => ?_, S, a, d, hX,
      fun h => hbd (Prod.mk.inj h).2⟩))
    rcases hNa w h1 with rfl | rfl
    · exact G.irrefl h2
    · exact hbd' h2

/-- A cut with exactly two crossing pairs gives a reduction. -/
lemma cut_two (S : Finset V) (h2 : (X G S).card = 2) : R0p G ∨ R1p G ∨ R2p G ∨ R3p G := by
  obtain ⟨⟨a, b⟩, ⟨c, d⟩, hpq, hX⟩ := card_eq_two.mp h2
  by_cases hac : a = c
  · subst hac
    exact cut_two_same_tail S hX fun h => hpq (by rw [h])
  by_cases hbd : b = d
  · subst hbd
    have hX' : X G Sᶜ = {(b, a), (b, c)} := by
      rw [X_compl, hX]
      simp [Finset.image_insert]
    exact cut_two_same_tail Sᶜ hX' hac
  · have habm : (a, b) ∈ X G S := by rw [hX]; simp
    have hcdm : (c, d) ∈ X G S := by rw [hX]; simp
    have hmem : ∀ x y, x ∈ S → y ∉ S → G.Adj x y → (x = a ∧ y = b) ∨ (x = c ∧ y = d) := by
      intro x y hx hy hxy
      have : (x, y) ∈ X G S := mem_X.mpr ⟨hx, hy, hxy⟩
      rw [hX] at this
      simpa using this
    rw [mem_X] at habm hcdm
    refine Or.inr (Or.inr (Or.inl ⟨a, b, habm.2.2, fun w ⟨h1, h2⟩ => ?_, S, c, d, hX, hpq⟩))
    by_cases hw : w ∈ S
    · rcases hmem w b hw habm.2.1 h2.symm with ⟨rfl, -⟩ | ⟨-, h⟩
      · exact G.irrefl h1
      · exact hbd h
    · rcases hmem a w habm.1 hw h1 with ⟨-, rfl⟩ | ⟨h, -⟩
      · exact G.irrefl h2
      · exact hac h

/-- **`ℤ₂³`-flows.** A graph in which every edge carries a nonzero `ℤ₂`-flow has a nowhere-zero
`ℤ₂³`-flow. -/
theorem gl_of_bl : ∀ G : SimpleGraph V, Bl G → Gl G := by
  suffices h : ∀ n, ∀ G : SimpleGraph V, G.edgeSet.ncard = n → Bl G → Gl G from
    fun G => h _ G rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G hn hG
  have IH : IndHyp G := fun G' h' hG' => ih _ (hn ▸ h') G' rfl hG'
  by_cases h0 : R0p G
  · exact gl_of_R0p h0
  by_cases h1 : R1p G
  · exact gl_of_R1p hG IH h1
  by_cases h2 : R2p G
  · exact gl_of_R2p hG IH h2
  by_cases h3 : R3p G
  · exact gl_of_R3p hG IH h3
  apply gl_base
  rintro S ⟨x, hx, y, hxy⟩ ⟨x', hx', y', hxy'⟩
  by_contra hlt
  have hc : (X G S).card = 0 ∨ (X G S).card = 1 ∨ (X G S).card = 2 := by omega
  rcases hc with hc | hc | hc
  · rw [card_eq_zero] at hc
    have hy : y ∈ S := by
      by_contra hy
      have : (x, y) ∈ X G S := mem_X.mpr ⟨hx, hy, hxy⟩
      simp [hc] at this
    have hy' : y' ∉ S := by
      intro hy'
      have : (y', x') ∈ X G S := mem_X.mpr ⟨hy', hx', hxy'.symm⟩
      simp [hc] at this
    refine h1 ⟨S, x, hx, fun u v hu hv huv => ?_, ⟨x, y, hxy, hx, hy⟩,
      ⟨x', y', hxy', fun h => hx' h.1⟩⟩
    have : (u, v) ∈ X G S := mem_X.mpr ⟨hu, hv, huv⟩
    simp [hc] at this
  · exact X_card_ne_one hG S hc
  · rcases cut_two S hc with h | h | h | h
    · exact h0 h
    · exact h1 h
    · exact h2 h
    · exact h3 h

end EightFlow
