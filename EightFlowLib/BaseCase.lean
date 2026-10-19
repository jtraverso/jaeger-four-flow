/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import EightFlowLib.FlowBasic
public import TreePackingLib.NashWilliams

/-!
# The three-edge-connected case

If every cut separating two edges of `G` is crossed by at least three edges, then `G` has a
nowhere-zero `ℤ₂³`-flow. Three connected spanning subgraphs of `G` with no common edge are
obtained from the tree packing theorem applied to an auxiliary graph (seven copies of every
vertex forming a clique and two copies of every edge), and their cotrees extend to three even
subgraphs covering `G`.
-/

@[expose] public section

open Finset SimpleGraph

attribute [local instance low] Classical.propDecidable

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace EightFlow

variable {V : Type*} [Fintype V]

/-- `W`-joins inside a set of mutually reachable vertices. -/
lemma exists_tJoin' (T : SimpleGraph V) (U : Finset V)
    (hT : ∀ u ∈ U, ∀ w ∈ U, T.Reachable u w) :
    ∀ n, ∀ W : Finset V, W ⊆ U → #W = 2 * n → ∃ J : SimpleGraph V, J ≤ T ∧
      ∃ _ : DecidableRel J.Adj, ∀ v, (Odd (J.degree v) ↔ v ∈ W) := by
  intro n
  induction n with
  | zero =>
    intro W _ hW
    rw [mul_zero, Finset.card_eq_zero] at hW
    subst hW
    exact ⟨⊥, bot_le, inferInstance, fun v => by simp⟩
  | succ n ih =>
    intro W hWU hW
    obtain ⟨u, hu⟩ : W.Nonempty := Finset.card_pos.mp (by omega)
    have h1 : #(W.erase u) = 2 * n + 1 := by rw [Finset.card_erase_of_mem hu]; omega
    obtain ⟨w, hw⟩ : (W.erase u).Nonempty := Finset.card_pos.mp (by omega)
    have h2 : #((W.erase u).erase w) = 2 * n := by rw [Finset.card_erase_of_mem hw]; omega
    obtain ⟨J', hJ', _, hJ'odd⟩ :=
      ih _ ((erase_subset _ _).trans ((erase_subset _ _).trans hWU)) h2
    have huw : u ≠ w := fun h => by simp [h] at hw
    have hwW : w ∈ W := Finset.mem_of_mem_erase hw
    obtain ⟨p, hp⟩ := (hT u (hWU hu) w (hWU hwW)).exists_isPath
    refine ⟨symmDiff J' (fromEdgeSet {e | e ∈ p.edges}),
      symmDiff_le_sup.trans (sup_le hJ' (Jaeger.walkGraph_le p)), inferInstance, fun v => ?_⟩
    rw [← ZMod.natCast_eq_one_iff_odd, Jaeger.degree_symmDiff_zmod,
      Jaeger.natCast_zmod_two_eq_ite (hJ'odd v), Jaeger.natCast_zmod_two_eq_ite
        (Jaeger.odd_degree_walkGraph_iff p hp huw v)]
    by_cases hvu : v = u
    · subst hvu; simp [hu, huw]
    by_cases hvw : v = w
    · subst hvw; simp [hwW, Ne.symm huw]
    simp [hvu, hvw]

/-- The auxiliary graph: seven copies of each vertex forming a clique, two copies of each edge
of `G`, and the copies of the vertices outside `U` attached to the copies of `u₀`. -/
abbrev aux (G : SimpleGraph V) (U : Finset V) (u₀ : V) : SimpleGraph (V × Fin 7) where
  Adj p q := (p.1 = q.1 ∧ p.2 ≠ q.2) ∨ (G.Adj p.1 q.1 ∧ p.2 = q.2 ∧ p.2.val < 2) ∨
    (p.2 = q.2 ∧ p.1 ≠ q.1 ∧ ((p.1 ∉ U ∧ q.1 = u₀) ∨ (q.1 ∉ U ∧ p.1 = u₀)))
  symm := ⟨fun p q h => by
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · exact Or.inl ⟨h1.symm, h2.symm⟩
    · exact Or.inr (Or.inl ⟨h1.symm, h2.symm, h2 ▸ h3⟩)
    · exact Or.inr (Or.inr ⟨h1.symm, h2.symm, h3.symm⟩)⟩
  loopless := ⟨fun p h => by
    rcases h with ⟨_, h⟩ | ⟨h, _⟩ | ⟨_, h, _⟩
    · exact h rfl
    · exact G.irrefl h
    · exact h rfl⟩

lemma six_le_encard {α : Type*} {s : Set α} (F : Finset α) (hF : 6 ≤ F.card)
    (hFs : ∀ e ∈ F, e ∈ s) : ¬ s.encard < 6 := by
  intro hs
  have h1 : ((F : Set α)).encard ≤ s.encard := Set.encard_le_encard fun e he => hFs e he
  rw [Set.encard_coe_eq_coe_finsetCard] at h1
  have h2 : (6 : ℕ∞) ≤ s.encard := le_trans (by exact_mod_cast hF) h1
  exact absurd hs (not_lt.mpr h2)

lemma aux_edgeConnected {G : SimpleGraph V} {U : Finset V} {u₀ : V} (hu₀ : u₀ ∈ U)
    (hU : ∀ v, v ∈ U ↔ ∃ w, G.Adj v w)
    (h : ∀ S : Finset V, (∃ x ∈ S, ∃ y, G.Adj x y) → (∃ x ∉ S, ∃ y, G.Adj x y) →
      3 ≤ (X G S).card) : (aux G U u₀).IsEdgeConnected 6 := by
  intro p q s hs
  by_contra hnr
  set A := aux G U u₀ with hA
  let P : Finset (V × Fin 7) := univ.filter fun r => (A.deleteEdges s).Reachable p r
  have hp : p ∈ P := by simp [P]
  have hq : q ∉ P := by simpa [P] using hnr
  have hcross : ∀ r r', r ∈ P → r' ∉ P → A.Adj r r' → s(r, r') ∈ s := by
    intro r r' hr hr' hadj
    by_contra hns
    simp only [P, mem_filter, mem_univ, true_and] at hr hr'
    exact hr' (hr.trans (Adj.reachable (by rw [deleteEdges_adj]; exact ⟨hadj, hns⟩)))
  by_cases hsplit : ∃ v i j, (v, i) ∈ P ∧ (v, j) ∉ P
  · obtain ⟨v, i, j, hi, hj⟩ := hsplit
    let I : Finset (Fin 7) := univ.filter fun k => (v, k) ∈ P
    have hinj : Set.InjOn (fun kl : Fin 7 × Fin 7 => s((v, kl.1), (v, kl.2)))
        ↑(I ×ˢ Iᶜ) := by
      rintro ⟨k, l⟩ hkl ⟨k', l'⟩ hkl' heq
      simp only [coe_product, Set.mem_prod, mem_coe, mem_compl, I, mem_filter, mem_univ,
        true_and] at hkl hkl'
      rcases Sym2.eq_iff.mp heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · simp only [Prod.mk.injEq, true_and] at h1 h2
        rw [h1, h2]
      · simp only [Prod.mk.injEq, true_and] at h1 h2
        exact absurd (h1 ▸ hkl.1) hkl'.2
    refine six_le_encard ((I ×ˢ Iᶜ).image fun kl => s((v, kl.1), (v, kl.2))) ?_ ?_ hs
    · rw [card_image_of_injOn hinj, card_product, card_compl, Fintype.card_fin]
      have h1 : 1 ≤ I.card := card_pos.mpr ⟨i, by simp [I, hi]⟩
      have h2 : I.card < 7 := by
        have : I.card < (univ : Finset (Fin 7)).card :=
          card_lt_card (ssubset_univ_iff.mpr fun h' => hj (by
            have : j ∈ I := h' ▸ mem_univ j
            simpa [I] using this))
        simpa using this
      interval_cases I.card <;> norm_num
    · intro e he
      obtain ⟨⟨k, l⟩, hkl, rfl⟩ := mem_image.mp he
      simp only [mem_product, mem_compl, I, mem_filter, mem_univ, true_and] at hkl
      exact hcross _ _ hkl.1 hkl.2
        (Or.inl ⟨rfl, fun h' => hkl.2 (by simp only at h'; rw [← h']; exact hkl.1)⟩)
  · push Not at hsplit
    let S : Finset V := univ.filter fun x => (x, 0) ∈ P
    have hmemS : ∀ x k, (x, k) ∈ P ↔ x ∈ S := by
      intro x k
      simp only [S, mem_filter, mem_univ, true_and]
      exact ⟨fun h' => hsplit x k 0 h', fun h' => hsplit x 0 k h'⟩
    have hpS : p.1 ∈ S := (hmemS p.1 p.2).mp hp
    have hqS : q.1 ∉ S := fun h' => hq ((hmemS q.1 q.2).mpr h')
    by_cases hUS : (∃ x ∈ S, x ∈ U) ∧ (∃ x ∉ S, x ∈ U)
    · obtain ⟨⟨x, hxS, hxU⟩, ⟨y, hyS, hyU⟩⟩ := hUS
      have h3 := h S ⟨x, hxS, (hU x).mp hxU⟩ ⟨y, hyS, (hU y).mp hyU⟩
      let J : Finset (Fin 7) := univ.filter fun j => j.val < 2
      have hJ : J.card = 2 := by decide
      have hinj : Set.InjOn
          (fun pj : (V × V) × Fin 7 => s((pj.1.1, pj.2), (pj.1.2, pj.2))) ↑(X G S ×ˢ J) := by
        rintro ⟨⟨a, b⟩, j⟩ hab ⟨⟨a', b'⟩, j'⟩ hab' heq
        simp only [coe_product, Set.mem_prod, mem_coe, mem_X] at hab hab'
        rcases Sym2.eq_iff.mp heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · simp only [Prod.mk.injEq] at h1 h2
          rw [h1.1, h1.2, h2.1]
        · simp only [Prod.mk.injEq] at h1 h2
          exact absurd (h1.1 ▸ hab.1.1) hab'.1.2.1
      refine six_le_encard ((X G S ×ˢ J).image
        fun pj => s((pj.1.1, pj.2), (pj.1.2, pj.2))) ?_ ?_ hs
      · rw [card_image_of_injOn hinj, card_product, hJ]
        omega
      · intro e he
        obtain ⟨⟨⟨a, b⟩, j⟩, hab, rfl⟩ := mem_image.mp he
        simp only [mem_product, mem_X, J, mem_filter, mem_univ, true_and] at hab
        exact hcross _ _ ((hmemS a j).mpr hab.1.1) (fun h' => hab.1.2.1 ((hmemS b j).mp h'))
          (Or.inr (Or.inl ⟨hab.1.2.2, rfl, hab.2⟩))
    · obtain ⟨v, hvU, hv⟩ : ∃ v, v ∉ U ∧ (v ∈ S ↔ u₀ ∉ S) := by
        by_cases hu₀S : u₀ ∈ S
        · exact ⟨q.1, fun hqU => hUS ⟨⟨u₀, hu₀S, hu₀⟩, ⟨q.1, hqS, hqU⟩⟩, by simp [hqS, hu₀S]⟩
        · exact ⟨p.1, fun hpU => hUS ⟨⟨p.1, hpS, hpU⟩, ⟨u₀, hu₀S, hu₀⟩⟩, by simp [hpS, hu₀S]⟩
      have hvu₀ : v ≠ u₀ := fun h' => hvU (h' ▸ hu₀)
      have hinj : Set.InjOn (fun k : Fin 7 => s((v, k), (u₀, k))) ↑(univ : Finset (Fin 7)) := by
        intro k _ k' _ heq
        rcases Sym2.eq_iff.mp heq with ⟨h1, -⟩ | ⟨h1, -⟩
        · exact (Prod.mk.inj h1).2
        · exact absurd (Prod.mk.inj h1).1 hvu₀
      refine six_le_encard (univ.image fun k : Fin 7 => s((v, k), (u₀, k))) ?_ ?_ hs
      · rw [card_image_of_injOn hinj, card_univ, Fintype.card_fin]
        omega
      · intro e he
        obtain ⟨k, -, rfl⟩ := mem_image.mp he
        by_cases hvS : v ∈ S
        · exact hcross _ _ ((hmemS v k).mpr hvS) (fun h' => hv.mp hvS ((hmemS u₀ k).mp h'))
            (Or.inr (Or.inr ⟨rfl, hvu₀, Or.inl ⟨hvU, rfl⟩⟩))
        · have hu₀S : u₀ ∈ S := by
            by_contra h'
            exact hvS (hv.mpr h')
          rw [Sym2.eq_swap]
          exact hcross _ _ ((hmemS u₀ k).mpr hu₀S) (fun h' => hvS ((hmemS v k).mp h'))
            (Or.inr (Or.inr ⟨rfl, Ne.symm hvu₀, Or.inr ⟨hvU, rfl⟩⟩))

lemma gl_base {G : SimpleGraph V}
    (h : ∀ S : Finset V, (∃ x ∈ S, ∃ y, G.Adj x y) → (∃ x ∉ S, ∃ y, G.Adj x y) →
      3 ≤ (X G S).card) : Gl G := by
  by_cases hE : ∃ x y, G.Adj x y
  swap
  · push Not at hE
    exact ⟨fun _ _ => 0, ⟨fun _ _ => by simp, fun _ _ _ => rfl, fun _ => by simp⟩,
      fun u v huv => absurd huv (hE u v)⟩
  obtain ⟨u₀, y₀, h₀⟩ := hE
  set U : Finset V := univ.filter fun v => ∃ w, G.Adj v w with hUdef
  have hU : ∀ v, v ∈ U ↔ ∃ w, G.Adj v w := by simp [U]
  have hu₀ : u₀ ∈ U := (hU u₀).mpr ⟨y₀, h₀⟩
  have : Nonempty (V × Fin 7) := ⟨(u₀, 0)⟩
  obtain ⟨T, hT, hdisj⟩ := NashWilliams.exists_trees_of_isEdgeConnected (aux G U u₀) 3
    (aux_edgeConnected hu₀ hU h)
  let C : Fin 3 → SimpleGraph V := fun i =>
    { Adj := fun x y => G.Adj x y ∧ ∃ j, (T i).Adj (x, j) (y, j)
      symm := ⟨fun x y hxy => ⟨hxy.1.symm, hxy.2.elim fun j hj => ⟨j, hj.symm⟩⟩⟩
      loopless := ⟨fun x hx => G.irrefl hx.1⟩ }
  have hCG : ∀ i, C i ≤ G := fun i x y hxy => hxy.1
  have hCreach : ∀ i, ∀ u ∈ U, ∀ w ∈ U, (C i).Reachable u w := by
    intro i u hu w hw
    let g : V × Fin 7 → V := fun p => if p.1 ∈ U then p.1 else u₀
    have hg : ∀ p q, (T i).Adj p q → (C i).Reachable (g p) (g q) := by
      intro p q hpq
      rcases (hT i).1 hpq with ⟨h1, -⟩ | ⟨h1, h2, -⟩ | ⟨-, -, h3⟩
      · have : g p = g q := by simp only [g, h1]
        rw [this]
      · have hpU : p.1 ∈ U := (hU _).mpr ⟨_, h1⟩
        have hqU : q.1 ∈ U := (hU _).mpr ⟨_, h1.symm⟩
        have : g p = p.1 := ite_eq_left hpU
        have : g q = q.1 := ite_eq_left hqU
        simp only [g, ite_eq_left hpU, ite_eq_left hqU]
        refine Adj.reachable ⟨h1, p.2, ?_⟩
        obtain ⟨a, j⟩ := p
        obtain ⟨b, k⟩ := q
        simp only at h2
        subst h2
        exact hpq
      · have : g p = g q := by
          rcases h3 with ⟨h3, h4⟩ | ⟨h3, h4⟩
          · simp only [g, ite_eq_right h3, h4, ite_eq_left hu₀]
          · simp only [g, ite_eq_right h3, h4, ite_eq_left hu₀]
        rw [this]
    have := NashWilliams.reachable_map_of_adj g hg ((hT i).2.connected.preconnected (u, 0) (w, 0))
    simpa [g, hu, hw] using this
  have hCcov : ∀ x y, G.Adj x y → ∃ i, ¬ (C i).Adj x y := by
    intro x y hxy
    by_contra hall
    push Not at hall
    have hj : ∀ i, ∃ j : Fin 7, j.val < 2 ∧ (T i).Adj (x, j) (y, j) := by
      intro i
      obtain ⟨-, j, hj⟩ := hall i
      refine ⟨j, ?_, hj⟩
      rcases (hT i).1 hj with ⟨h1, -⟩ | ⟨-, -, h3⟩ | ⟨-, -, h3⟩
      · exact absurd h1 hxy.ne
      · exact h3
      · rcases h3 with ⟨h3, -⟩ | ⟨h3, -⟩
        · exact absurd ((hU x).mpr ⟨y, hxy⟩) h3
        · exact absurd ((hU y).mpr ⟨x, hxy.symm⟩) h3
    obtain ⟨j₀, hj₀, h₀⟩ := hj 0
    obtain ⟨j₁, hj₁, h₁⟩ := hj 1
    obtain ⟨j₂, hj₂, h₂⟩ := hj 2
    have hd : ∀ i k : Fin 3, i ≠ k → ∀ j : Fin 7, (T i).Adj (x, j) (y, j) →
        ¬ (T k).Adj (x, j) (y, j) :=
      fun i k hik j hi hk => NashWilliams.disjoint_iff_adj.mp (hdisj hik) _ _ hi hk
    by_cases e01 : j₀ = j₁
    · exact hd 0 1 (by decide) j₀ h₀ (e01 ▸ h₁)
    by_cases e02 : j₀ = j₂
    · exact hd 0 2 (by decide) j₀ h₀ (e02 ▸ h₂)
    have e12 : j₁ = j₂ := by
      apply Fin.ext
      have := Fin.val_ne_of_ne e01
      have := Fin.val_ne_of_ne e02
      omega
    exact hd 1 2 (by decide) j₁ h₁ (e12 ▸ h₂)
  have key : ∀ i, ∃ H : SimpleGraph V, H ≤ G ∧ G \ C i ≤ H ∧ ∀ v, Even (H.degree v) := by
    intro i
    obtain ⟨n, hn⟩ := even_card_odd_degree_vertices (G \ C i)
    obtain ⟨J, hJT, _, hJ⟩ := exists_tJoin' (C i) U (hCreach i) n
      (univ.filter fun v => Odd ((G \ C i).degree v)) (fun v hv => by
        rw [mem_filter] at hv
        obtain ⟨w, hw⟩ := (G \ C i).degree_pos_iff_exists_adj v |>.mp hv.2.pos
        exact (hU v).mpr ⟨w, hw.1⟩) (by rw [hn]; ring)
    refine ⟨symmDiff (G \ C i) J,
      symmDiff_le_sup.trans (sup_le sdiff_le (hJT.trans (hCG i))), fun a b hab => ?_,
      fun v => ?_⟩
    · have hJ' : ¬ J.Adj a b := fun h' => hab.2 (hJT h')
      simp only [symmDiff, sup_adj, sdiff_adj]
      exact Or.inl ⟨hab, hJ'⟩
    · rw [← ZMod.natCast_eq_zero_iff_even, Jaeger.degree_symmDiff_zmod,
        Jaeger.natCast_zmod_two_eq_ite (hJ v),
        Jaeger.natCast_zmod_two_eq_ite (P := v ∈ univ.filter fun v => Odd ((G \ C i).degree v))
          (by simp)]
      split_ifs <;> rfl
  choose H hHG hGH hHe using key
  refine ⟨fun u v i => if (H i).Adj u v then 1 else 0, ⟨fun u v => ?_, fun u v huv => ?_,
    fun v => ?_⟩, fun u v huv => ?_⟩
  · rw [neg_eq_of_add_self m3_add_self]
    funext i
    simp only [(H i).adj_comm v u]
  · funext i
    simp only [Pi.zero_apply]
    rw [ite_eq_right fun h' => huv (hHG i h')]
  · funext i
    rw [Finset.sum_apply, Pi.zero_apply]
    have := hHe i v
    rw [← ZMod.natCast_eq_zero_iff_even, Jaeger.degree_cast_zmod] at this
    convert this
  · obtain ⟨i, hi⟩ := hCcov u v huv
    intro h0
    have := congrFun h0 i
    simp only [Pi.zero_apply] at this
    rw [ite_eq_left (hGH i ⟨huv, hi⟩)] at this
    exact one_ne_zero this

end EightFlow
