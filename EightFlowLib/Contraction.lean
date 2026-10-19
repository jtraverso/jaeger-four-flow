/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import EightFlowLib.Reductions

/-!
# Contracting an edge of a two-edge cut

If `s(a, b)` lies in a cut with exactly two crossing edges and `a`, `b` have no common neighbour,
the graph obtained by merging `b` into `a` is simple, has fewer edges, inherits the `ℤ₂`-flow
condition, and a nowhere-zero `ℤ₂³`-flow of it lifts back.
-/

@[expose] public section

open Finset SimpleGraph

attribute [local instance low] Classical.propDecidable

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace EightFlow

variable {V : Type*} [Fintype V]

/-- The quotient graph along a map `π` (loops removed). -/
abbrev quot (G : SimpleGraph V) (π : V → V) : SimpleGraph V where
  Adj u v := u ≠ v ∧ ∃ x y, G.Adj x y ∧ π x = u ∧ π y = v
  symm := ⟨fun _ _ ⟨h, x, y, hxy, hx, hy⟩ => ⟨h.symm, y, x, hxy.symm, hy, hx⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

variable {M : Type*} [AddCommGroup M]

/-- Total value from the fibre of `u` to the fibre of `v`. -/
noncomputable def blk (π : V → V) (f : V → V → M) (u v : V) : M :=
  ∑ x ∈ univ.filter (π · = u), ∑ y ∈ univ.filter (π · = v), f x y

/-- Push-forward of a flow along `π`. -/
noncomputable def push (π : V → V) (f : V → V → M) : V → V → M :=
  fun u v => if u = v then 0 else blk π f u v

lemma isFl_push {G : SimpleGraph V} {f : V → V → M} (hf : IsFl G f) (π : V → V) :
    IsFl (quot G π) (push π f) := by
  refine ⟨fun u v => ?_, fun u v huv => ?_, fun u => ?_⟩
  · unfold push
    by_cases h : u = v
    · subst h; simp
    · rw [ite_eq_right (Ne.symm h), ite_eq_right h, blk, blk, Finset.sum_comm,
        ← Finset.sum_neg_distrib]
      refine sum_congr rfl fun x _ => ?_
      rw [← Finset.sum_neg_distrib]
      exact sum_congr rfl fun y _ => hf.1 _ _
  · unfold push
    split_ifs with h
    · rfl
    · refine sum_eq_zero fun x hx => sum_eq_zero fun y hy => hf.2.1 _ _ fun hxy => ?_
      exact huv ⟨h, x, y, hxy, (mem_filter.mp hx).2, (mem_filter.mp hy).2⟩
  · have h1 : ∑ v, blk π f u v = 0 := by
      unfold blk
      rw [Finset.sum_comm]
      refine sum_eq_zero fun x _ => ?_
      rw [Finset.sum_fiberwise univ π (f x)]
      exact hf.2.2 x
    have h2 : blk π f u u = 0 := sum_block_eq_zero hf.1 hf.diag _
    have : ∀ v, push π f u v = blk π f u v - if u = v then blk π f u v else 0 := by
      intro v; unfold push; split_ifs <;> simp
    simp_rw [this]
    rw [sum_sub_distrib, h1, sum_ite_eq, ite_eq_left (mem_univ _), h2, sub_zero]

/-- Merge `b` into `a`. -/
noncomputable def piab (a b : V) (x : V) : V := if x = b then a else x

section contraction

variable {a b : V}

omit [Fintype V] in
lemma piab_b : piab a b b = a := by simp [piab]

omit [Fintype V] in
lemma piab_of_ne {x : V} (hx : x ≠ b) : piab a b x = x := by simp [piab, hx]

omit [Fintype V] in
lemma piab_ne_b (hab : a ≠ b) (x : V) : piab a b x ≠ b := by
  unfold piab; split_ifs with h
  · exact hab
  · exact h

omit [Fintype V] in
lemma piab_eq_iff (hab : a ≠ b) {x x' : V} :
    piab a b x = piab a b x' ↔ x = x' ∨ (x = a ∧ x' = b) ∨ (x = b ∧ x' = a) := by
  unfold piab
  split_ifs with h1 h2 h2 <;> subst_vars <;> tauto

omit [Fintype V] in
lemma piab_eq_a_iff {x : V} : piab a b x = a ↔ x = a ∨ x = b := by
  unfold piab; split_ifs with h <;> tauto

omit [Fintype V] in
lemma piab_eq_v_iff {v x : V} (hva : v ≠ a) (hvb : v ≠ b) : piab a b x = v ↔ x = v := by
  unfold piab; split_ifs with h
  · subst h; exact ⟨fun h' => absurd h'.symm hva, fun h' => absurd h'.symm hvb⟩
  · rfl

variable {G : SimpleGraph V}

omit [Fintype V] in
lemma collide (hab : G.Adj a b) (hcn : ∀ w, ¬ (G.Adj a w ∧ G.Adj b w)) {x y x' y' : V}
    (h1 : G.Adj x y) (h2 : G.Adj x' y') (hx : piab a b x = piab a b x')
    (hy : piab a b y = piab a b y') (hne : piab a b x ≠ piab a b y) : x = x' ∧ y = y' := by
  rw [piab_eq_iff hab.ne] at hx hy
  rcases hx with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hy with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals first
    | exact ⟨rfl, rfl⟩
    | exact (G.irrefl h1).elim
    | exact (G.irrefl h2).elim
    | exact (hcn _ ⟨h1.symm, h2.symm⟩).elim
    | exact (hcn _ ⟨h2.symm, h1.symm⟩).elim
    | exact (hcn _ ⟨h1, h2⟩).elim
    | exact (hcn _ ⟨h2, h1⟩).elim
    | exact (hne (by simp [piab])).elim

omit [Fintype V] in
lemma piab_ne_of_adj (hab : a ≠ b) {x y : V} (h : G.Adj x y) (hne : s(x, y) ≠ s(a, b)) :
    piab a b x ≠ piab a b y := by
  rw [Ne, piab_eq_iff hab]
  rintro (rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
  · exact G.irrefl h
  · exact hne rfl
  · exact hne Sym2.eq_swap

omit [Fintype V] in
lemma quot_adj_of_adj (hab : a ≠ b) {x y : V} (h : G.Adj x y) (hne : s(x, y) ≠ s(a, b)) :
    (quot G (piab a b)).Adj (piab a b x) (piab a b y) :=
  ⟨piab_ne_of_adj hab h hne, x, y, h, rfl, rfl⟩

lemma bl_quot (hG : Bl G) (hab : G.Adj a b) (hcn : ∀ w, ¬ (G.Adj a w ∧ G.Adj b w)) :
    Bl (quot G (piab a b)) := by
  rintro u v ⟨huv, x, y, hxy, rfl, rfl⟩
  obtain ⟨ψ, hψ, hne⟩ := hG x y hxy
  refine ⟨push (piab a b) ψ, isFl_push hψ _, ?_⟩
  rw [push, ite_eq_right huv, blk, sum_eq_single_of_mem x (by simp) ?_,
    sum_eq_single_of_mem y (by simp) ?_]
  · exact hne
  · intro y' hy' hne'
    refine hψ.2.1 _ _ fun h' => hne' ?_
    exact (collide hab hcn hxy h' rfl (mem_filter.mp hy').2.symm huv).2.symm
  · intro x' hx' hne'
    refine sum_eq_zero fun y' hy' => hψ.2.1 _ _ fun h' => hne' ?_
    exact (collide hab hcn hxy h' (mem_filter.mp hx').2.symm (mem_filter.mp hy').2.symm
      huv).1.symm

omit [Fintype V] in
lemma ncard_quot_lt [Finite V] (hab : G.Adj a b) :
    (quot G (piab a b)).edgeSet.ncard < G.edgeSet.ncard := by
  have hsub : (quot G (piab a b)).edgeSet ⊆ Sym2.map (piab a b) '' (G.edgeSet \ {s(a, b)}) := by
    intro e he
    induction e using Sym2.ind with
    | _ u v =>
      rw [mem_edgeSet] at he
      obtain ⟨huv, x, y, hxy, rfl, rfl⟩ := he
      refine ⟨s(x, y), ⟨hxy, fun h => ?_⟩, rfl⟩
      rw [Set.mem_singleton_iff] at h
      rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact huv (by rw [piab_b, piab_of_ne hab.ne])
      · exact huv (by rw [piab_b, piab_of_ne hab.ne])
  calc _ ≤ (Sym2.map (piab a b) '' (G.edgeSet \ {s(a, b)})).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ (G.edgeSet \ {s(a, b)}).ncard := Set.ncard_image_le (Set.toFinite _)
    _ < G.edgeSet.ncard := Set.ncard_sdiff_singleton_lt_of_mem hab (Set.toFinite _)

lemma sum_split_ab (hab : a ≠ b) (g : V → M) :
    ∑ y, g y = g a + g b + ∑ y ∈ (univ.erase a).erase b, g y := by
  rw [← add_sum_erase univ g (mem_univ a),
    ← add_sum_erase (univ.erase a) g (mem_erase.mpr ⟨hab.symm, mem_univ b⟩), add_assoc]

lemma mem_rest {y : V} : y ∈ (univ.erase a).erase b ↔ y ≠ a ∧ y ≠ b := by
  simp [and_comm]

/-- Lifting a nowhere-zero `ℤ₂³`-flow from the contraction. -/
lemma gl_lift (hab : G.Adj a b) (hcn : ∀ w, ¬ (G.Adj a w ∧ G.Adj b w)) {S : Finset V}
    {c d : V} (hX : X G S = {(a, b), (c, d)}) (hcd : (a, b) ≠ (c, d)) {ℓ' : V → V → M3}
    (hℓ' : IsFl (quot G (piab a b)) ℓ') (hn' : ∀ u v, (quot G (piab a b)).Adj u v → ℓ' u v ≠ 0) :
    Gl G := by
  have hab' : a ≠ b := hab.ne
  set π := piab a b with hπ
  have hsym : ∀ u v, ℓ' v u = ℓ' u v := fun u v => by
    rw [hℓ'.1, neg_eq_of_add_self m3_add_self]
  have hπa : π a = a := piab_of_ne hab'
  have hπb : π b = a := piab_b
  have hπy : ∀ y, y ≠ b → π y = y := fun y hy => piab_of_ne hy
  have qb : ∀ x, ℓ' x b = 0 := fun x => hℓ'.2.1 _ _ fun ⟨_, _, y', _, _, hy⟩ =>
    piab_ne_b hab' y' hy
  have qa : ∀ v, v ≠ a → v ≠ b → ((quot G π).Adj a v ↔ G.Adj a v ∨ G.Adj b v) := by
    intro v hva hvb
    constructor
    · rintro ⟨-, x, y, hxy, hx, hy⟩
      rw [piab_eq_a_iff] at hx
      rw [piab_eq_v_iff hva hvb] at hy
      subst hy
      rcases hx with rfl | rfl
      · exact Or.inl hxy
      · exact Or.inr hxy
    · rintro (h | h)
      · exact ⟨Ne.symm hva, a, v, h, hπa, hπy v hvb⟩
      · exact ⟨Ne.symm hva, b, v, h, hπb, hπy v hvb⟩
  have qo : ∀ x v, x ≠ a → x ≠ b → v ≠ a → v ≠ b → ((quot G π).Adj x v ↔ G.Adj x v) := by
    intro x v hxa hxb hva hvb
    constructor
    · rintro ⟨-, x', y', hxy, hx, hy⟩
      rw [piab_eq_v_iff hxa hxb] at hx
      rw [piab_eq_v_iff hva hvb] at hy
      subst hx hy
      exact hxy
    · intro h
      exact ⟨h.ne, x, v, h, hπy x hxb, hπy v hvb⟩
  -- splitting `ℓ' a v` and `ℓ' x a` according to the preimage
  have splitA : ∀ v, v ≠ a → v ≠ b →
      ℓ' a v = (if G.Adj a v then ℓ' a v else 0) + (if G.Adj b v then ℓ' a v else 0) := by
    intro v hva hvb
    by_cases h1 : G.Adj a v <;> by_cases h2 : G.Adj b v
    · exact (hcn v ⟨h1, h2⟩).elim
    · simp [h1, h2]
    · simp [h1, h2]
    · simp only [h1, h2, ite_false, add_zero]
      exact hℓ'.2.1 _ _ fun h => (((qa v hva hvb).mp h).elim h1 h2)
  let t : M3 := ∑ y ∈ (univ.erase a).erase b, if G.Adj a y then ℓ' a y else 0
  let ℓ : V → V → M3 := fun x y =>
    if G.Adj x y then (if s(x, y) = s(a, b) then t else ℓ' (π x) (π y)) else 0
  have hℓab : ℓ a b = t := by simp [ℓ, hab]
  have hℓ_of : ∀ x y, G.Adj x y → s(x, y) ≠ s(a, b) → ℓ x y = ℓ' (π x) (π y) := by
    intro x y h hne
    simp only [ℓ]
    rw [ite_eq_left h, ite_eq_right hne]
  have hflow : IsFl G ℓ := by
    refine ⟨fun u v => ?_, fun u v huv => by simp [ℓ, huv], fun x => ?_⟩
    · rw [neg_eq_of_add_self m3_add_self]
      simp only [ℓ, G.adj_comm v u, Sym2.eq_swap (a := v), hsym]
    · rw [sum_split_ab hab']
      have hrest : ∀ y ∈ (univ.erase a).erase b,
          ℓ x y = if G.Adj x y then ℓ' (π x) y else 0 := by
        intro y hy
        rw [mem_rest] at hy
        by_cases h : G.Adj x y
        · rw [hℓ_of x y h (fun he => by
            rcases Sym2.eq_iff.mp he with ⟨-, h'⟩ | ⟨-, h'⟩
            · exact hy.2 h'
            · exact hy.1 h'), hπy y hy.2, ite_eq_left h]
        · simp [ℓ, h]
      rw [sum_congr rfl hrest]
      by_cases hxa : x = a
      · subst x
        rw [hℓab]
        simp only [ℓ, G.irrefl, ite_false, zero_add, hπa]
        exact m3_add_self t
      by_cases hxb : x = b
      · subst x
        have hba : ℓ b a = t := by simp [ℓ, hab.symm]
        rw [hba, show ℓ b b = 0 by simp [ℓ], add_zero, hπb]
        have h0 := hℓ'.2.2 a
        rw [sum_split_ab hab', hℓ'.diag, qb, zero_add, zero_add,
          sum_congr rfl fun y hy => splitA y (mem_rest.mp hy).1 (mem_rest.mp hy).2,
          sum_add_distrib] at h0
        exact h0
      · have h0 := hℓ'.2.2 x
        rw [sum_split_ab hab', qb, add_zero] at h0
        rw [hπy x hxb]
        have hra : ℓ x a + ℓ x b = ℓ' x a := by
          by_cases h1 : G.Adj x a <;> by_cases h2 : G.Adj x b
          · exact (hcn x ⟨h1.symm, h2.symm⟩).elim
          · have hne : s(x, a) ≠ s(a, b) := fun he => by
              rcases Sym2.eq_iff.mp he with ⟨h', -⟩ | ⟨h', -⟩
              · exact hxa h'
              · exact hxb h'
            rw [hℓ_of x a h1 hne, show ℓ x b = 0 by simp [ℓ, h2], add_zero, hπy x hxb, hπa]
          · have hne : s(x, b) ≠ s(a, b) := fun he => by
              rcases Sym2.eq_iff.mp he with ⟨h', -⟩ | ⟨h', -⟩
              · exact hxa h'
              · exact hxb h'
            rw [hℓ_of x b h2 hne, show ℓ x a = 0 by simp [ℓ, h1], zero_add, hπy x hxb, hπb]
          · rw [show ℓ x a = 0 by simp [ℓ, h1], show ℓ x b = 0 by simp [ℓ, h2], add_zero]
            symm
            refine hℓ'.2.1 _ _ fun h => ?_
            rcases (qa x hxa hxb).mp h.symm with h | h
            · exact h1 h.symm
            · exact h2 h.symm
        rw [hra]
        convert h0 using 2
        refine sum_congr rfl fun y hy => ?_
        rw [mem_rest] at hy
        by_cases h : G.Adj x y
        · rw [ite_eq_left h]
        · rw [ite_eq_right h]
          symm
          exact hℓ'.2.1 _ _ fun h' => h ((qo x y hxa hxb hy.1 hy.2).mp h')
  refine ⟨ℓ, hflow, fun x y hxy => ?_⟩
  have hcdm : (c, d) ∈ X G S := by rw [hX]; simp
  have habm : (a, b) ∈ X G S := by rw [hX]; simp
  rw [mem_X] at hcdm habm
  have hcd' : s(c, d) ≠ s(a, b) := by
    intro he
    rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hcd rfl
    · exact habm.2.1 hcdm.1
  have hcut := cut_sum_X hflow S
  rw [hX, sum_pair hcd, hℓab, hℓ_of c d hcdm.2.2 hcd'] at hcut
  by_cases he : s(x, y) = s(a, b)
  · have : ℓ x y = t := by simp only [ℓ]; rw [ite_eq_left hxy, ite_eq_left he]
    rw [this]
    intro ht
    rw [ht, zero_add] at hcut
    exact hn' _ _ (quot_adj_of_adj hab' hcdm.2.2 hcd') hcut
  · rw [hℓ_of x y hxy he]
    exact hn' _ _ (quot_adj_of_adj hab' hxy he)

end contraction

/-- An edge without common neighbours in a cut with exactly two crossing edges. -/
def R2p (G : SimpleGraph V) : Prop :=
  ∃ a b, G.Adj a b ∧ (∀ w, ¬ (G.Adj a w ∧ G.Adj b w)) ∧
    ∃ S : Finset V, ∃ c d, X G S = {(a, b), (c, d)} ∧ (a, b) ≠ (c, d)

lemma gl_of_R2p {G : SimpleGraph V} (hG : Bl G) (IH : IndHyp G) (h : R2p G) : Gl G := by
  obtain ⟨a, b, hab, hcn, S, c, d, hX, hcd⟩ := h
  obtain ⟨ℓ', hℓ', hn'⟩ := IH _ (ncard_quot_lt hab) (bl_quot hG hab hcn)
  exact gl_lift hab hcn hX hcd hℓ' hn'

end EightFlow
