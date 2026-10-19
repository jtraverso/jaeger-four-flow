/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import EightFlowLib.FlowBasic

/-!
# Reductions for the `ℤ₂³`-flow theorem

Even graphs, splitting along a cut whose crossing edges share an endpoint, and deleting the two
edges of a degree-two vertex lying on a triangle.
-/

@[expose] public section

open Finset SimpleGraph

attribute [local instance low] Classical.propDecidable

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace EightFlow

variable {V : Type*} [Fintype V]

/-- The induction hypothesis used throughout. -/
def IndHyp (G : SimpleGraph V) : Prop :=
  ∀ G' : SimpleGraph V, G'.edgeSet.ncard < G.edgeSet.ncard → Bl G' → Gl G'

omit [Fintype V] in
lemma ncard_lt_of_le [Finite V] {G G' : SimpleGraph V} (hle : G' ≤ G) {x y : V} (hxy : G.Adj x y)
    (hn : ¬ G'.Adj x y) : G'.edgeSet.ncard < G.edgeSet.ncard := by
  refine Set.ncard_lt_ncard ?_ (Set.toFinite _)
  rw [edgeSet_ssubset_edgeSet]
  exact lt_of_le_of_ne hle fun h => hn (h ▸ hxy)

variable {M : Type*} [AddCommGroup M]

/-- Strengthening the support condition of a flow. -/
lemma IsFl.restrict {G G' : SimpleGraph V} {f : V → V → M} (hf : IsFl G f)
    (h : ∀ u v, G.Adj u v → ¬ G'.Adj u v → f u v = 0) : IsFl G' f := by
  refine ⟨hf.1, fun u v huv => ?_, hf.2.2⟩
  by_cases hg : G.Adj u v
  · exact h u v hg huv
  · exact hf.2.1 u v hg

/-! ### Even graphs -/

/-- Every vertex has even degree. -/
def R0p (G : SimpleGraph V) : Prop := ∀ v, Even (G.degree v)

/-- The basis vector `e₀` of `ℤ₂³`. -/
def e0 : M3 := Pi.single 0 1
/-- The basis vector `e₁` of `ℤ₂³`. -/
def e1 : M3 := Pi.single 1 1

lemma e0_ne_zero : e0 ≠ 0 := by decide
lemma e1_ne_zero : e1 ≠ 0 := by decide
lemma e0_ne_e1 : e0 ≠ e1 := by decide

lemma gl_of_R0p {G : SimpleGraph V} (h : R0p G) : Gl G := by
  refine ⟨fun x y => if G.Adj x y then e0 else 0, ⟨fun u v => ?_, fun u v huv => ?_,
    fun v => ?_⟩, fun u v huv => ?_⟩
  · simp only [G.adj_comm v u]
    split_ifs
    · exact (neg_eq_of_add_self m3_add_self _).symm
    · simp
  · simp [huv]
  · rw [← Finset.sum_filter, sum_const, ← neighborFinset_eq_filter, card_neighborFinset_eq_degree]
    obtain ⟨k, hk⟩ := h v
    rw [hk, add_smul, ← smul_add, m3_add_self, smul_zero]
  · simp [huv, e0_ne_zero]

/-! ### Splitting -/

/-- `G` restricted to pairs inside `S`. -/
abbrev ind (G : SimpleGraph V) (S : Finset V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ u ∈ S ∧ v ∈ S
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩

/-- The edges of `G` not inside `S`. -/
abbrev outer (G : SimpleGraph V) (S : Finset V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ ¬ (u ∈ S ∧ v ∈ S)
  symm := ⟨fun _ _ h => ⟨h.1.symm, fun h' => h.2 ⟨h'.2, h'.1⟩⟩⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩

omit [Fintype V] in
lemma ind_le (G : SimpleGraph V) (S : Finset V) : ind G S ≤ G := fun _ _ h => h.1
omit [Fintype V] in
lemma outer_le (G : SimpleGraph V) (S : Finset V) : outer G S ≤ G := fun _ _ h => h.1

/-- Restriction of a function to `S × S`. -/
noncomputable def res (S : Finset V) (f : V → V → M) : V → V → M :=
  fun u v => if u ∈ S ∧ v ∈ S then f u v else 0

lemma isFl_res {G : SimpleGraph V} {f : V → V → M} (hf : IsFl G f) (S : Finset V)
    (h : ∀ v ∈ S, ∑ w ∈ Sᶜ, f v w = 0) : IsFl (ind G S) (res S f) := by
  refine ⟨fun u v => ?_, fun u v huv => ?_, fun v => ?_⟩
  · unfold res
    by_cases hu : u ∈ S <;> by_cases hv : v ∈ S <;> simp [hu, hv, hf.1 u v]
  · unfold res
    split_ifs with hs
    · exact hf.2.1 u v fun h' => huv ⟨h', hs⟩
    · rfl
  · unfold res
    by_cases hv : v ∈ S
    · simp only [hv, true_and]
      rw [Finset.sum_ite_mem, univ_inter]
      have := sum_add_sum_compl S (f v)
      rw [hf.2.2 v, h v hv, add_zero] at this
      exact this
    · simp [hv]

lemma isFl_res_compl {G : SimpleGraph V} {f : V → V → M} (hf : IsFl G f) (S : Finset V)
    (hr : IsFl (ind G S) (res S f)) : IsFl (outer G S) (fun u v => f u v - res S f u v) := by
  refine (hf.sub (hr.mono (ind_le G S))).restrict fun u v _ huv => ?_
  have : u ∈ S ∧ v ∈ S := by
    by_contra h'
    exact huv ⟨‹G.Adj u v›, h'⟩
  simp [res, this]

/-- A cut whose crossing pairs all start at `z ∈ S`, with edges on both sides. -/
def R1p (G : SimpleGraph V) : Prop :=
  ∃ S : Finset V, ∃ z ∈ S, (∀ x y, x ∈ S → y ∉ S → G.Adj x y → x = z) ∧
    (∃ x y, G.Adj x y ∧ x ∈ S ∧ y ∈ S) ∧ (∃ x y, G.Adj x y ∧ ¬ (x ∈ S ∧ y ∈ S))

lemma R1_cond {G : SimpleGraph V} {S : Finset V} {z : V} (hz : z ∈ S)
    (hc : ∀ x y, x ∈ S → y ∉ S → G.Adj x y → x = z) {f : V → V → M} (hf : IsFl G f) :
    ∀ v ∈ S, ∑ w ∈ Sᶜ, f v w = 0 := by
  have hzero : ∀ v ∈ S, v ≠ z → ∀ w ∈ Sᶜ, f v w = 0 := by
    intro v hv hvz w hw
    by_contra hne
    exact hvz (hc v w hv (by simpa using hw) (by_contra fun h => hne (hf.2.1 v w h)))
  intro v hv
  by_cases hvz : v = z
  · subst hvz
    have := cut_sum hf S
    rwa [Finset.sum_eq_single_of_mem v hv fun x hx hxz =>
      sum_eq_zero fun w hw => hzero x hx hxz w hw] at this
  · exact sum_eq_zero fun w hw => hzero v hv hvz w hw

lemma gl_of_R1p {G : SimpleGraph V} (hG : Bl G) (IH : IndHyp G) (h : R1p G) : Gl G := by
  obtain ⟨S, z, hz, hc, ⟨x₁, y₁, h₁, hx₁, hy₁⟩, ⟨x₂, y₂, h₂, hn₂⟩⟩ := h
  have hBl1 : Bl (ind G S) := by
    intro u v huv
    obtain ⟨ψ, hψ, hne⟩ := hG u v huv.1
    exact ⟨res S ψ, isFl_res hψ S (R1_cond hz hc hψ), by simp [res, huv.2, hne]⟩
  have hBl2 : Bl (outer G S) := by
    intro u v huv
    obtain ⟨ψ, hψ, hne⟩ := hG u v huv.1
    exact ⟨_, isFl_res_compl hψ S (isFl_res hψ S (R1_cond hz hc hψ)),
      by simp [res, huv.2, hne]⟩
  obtain ⟨ℓ₁, hℓ₁, hn₁⟩ := IH _ (ncard_lt_of_le (ind_le G S) h₂ fun h => hn₂ h.2) hBl1
  obtain ⟨ℓ₂, hℓ₂, hn₂'⟩ := IH _ (ncard_lt_of_le (outer_le G S) h₁ fun h => h.2 ⟨hx₁, hy₁⟩)
    hBl2
  refine ⟨_, (hℓ₁.mono (ind_le G S)).add (hℓ₂.mono (outer_le G S)), fun u v huv => ?_⟩
  by_cases hs : u ∈ S ∧ v ∈ S
  · rw [hℓ₂.2.1 u v fun h => h.2 hs, add_zero]
    exact hn₁ u v ⟨huv, hs⟩
  · rw [hℓ₁.2.1 u v fun h => hs h.2, zero_add]
    exact hn₂' u v ⟨huv, hs⟩

/-! ### Triangles -/

lemma sum_edge_ind {p q : V} (hpq : p ≠ q) (α : M) (v : V) :
    ∑ w, (if s(v, w) = s(p, q) then α else 0) =
      (if v = p then α else 0) + (if v = q then α else 0) := by
  by_cases hp : v = p
  · subst hp
    simp [hpq]
  · by_cases hq : v = q
    · subst hq
      simp [hp]
    · simp [hp, hq]

/-- The flow of value `α` around the triangle `a b d`. -/
noncomputable def tri (a b d : V) (α : M) : V → V → M := fun x y =>
  (if s(x, y) = s(a, b) then α else 0) + (if s(x, y) = s(a, d) then α else 0) +
    (if s(x, y) = s(b, d) then α else 0)

lemma isFl_tri {G : SimpleGraph V} {a b d : V} (hab : G.Adj a b) (had : G.Adj a d)
    (hbd : G.Adj b d) (α : M) (h2 : α + α = 0) : IsFl G (tri a b d α) := by
  refine ⟨fun u v => ?_, fun u v huv => ?_, fun v => ?_⟩
  · have hn : ∀ x : M, x + x = 0 → -x = x := fun x hx => by rw [neg_eq_iff_add_eq_zero, hx]
    unfold tri
    rw [Sym2.eq_swap (a := v)]
    split_ifs <;> simp [hn α h2, h2]
  · unfold tri
    have h1 : s(u, v) ≠ s(a, b) := fun h => huv (by rw [← mem_edgeSet, h]; exact hab)
    have h2' : s(u, v) ≠ s(a, d) := fun h => huv (by rw [← mem_edgeSet, h]; exact had)
    have h3 : s(u, v) ≠ s(b, d) := fun h => huv (by rw [← mem_edgeSet, h]; exact hbd)
    simp [h1, h2', h3]
  · unfold tri
    rw [sum_add_distrib, sum_add_distrib, sum_edge_ind hab.ne, sum_edge_ind had.ne,
      sum_edge_ind hbd.ne]
    have e : ∀ A B D : M, A + B + (A + D) + (B + D) = (A + A) + (B + B) + (D + D) :=
      fun _ _ _ => by abel
    rw [e]
    split_ifs <;> simp [h2]

/-- `G` with all edges at `a` deleted. -/
abbrev isoA (G : SimpleGraph V) (a : V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ x ≠ a ∧ y ≠ a
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩

omit [Fintype V] in
lemma isoA_le (G : SimpleGraph V) (a : V) : isoA G a ≤ G := fun _ _ h => h.1

/-- A degree-two vertex `a` on a triangle `a b d` such that `s(b, d)` still carries a
`ℤ₂`-flow after deleting the edges at `a`. -/
def R3p (G : SimpleGraph V) : Prop :=
  ∃ a b d, G.Adj a b ∧ G.Adj a d ∧ G.Adj b d ∧ (∀ w, G.Adj a w → w = b ∨ w = d) ∧
    ∃ ψ : V → V → ZMod 2, IsFl (isoA G a) ψ ∧ ψ b d ≠ 0

omit [Fintype V] in
lemma tri_eq_zero {a b d x y : V} (α : M) (h1 : s(x, y) ≠ s(a, b)) (h2 : s(x, y) ≠ s(a, d))
    (h3 : s(x, y) ≠ s(b, d)) : tri a b d α x y = 0 := by
  simp [tri, h1, h2, h3]

lemma gl_of_R3p {G : SimpleGraph V} (hG : Bl G) (IH : IndHyp G) (h : R3p G) : Gl G := by
  obtain ⟨a, b, d, hab, had, hbd, hN, ψ₀, hψ₀, hne₀⟩ := h
  have hbd' : b ≠ d := hbd.ne
  have hab' : a ≠ b := hab.ne
  have had' : a ≠ d := had.ne
  have e_ab_ad : s(a, b) ≠ s(a, d) := by rw [Ne, Sym2.eq_iff]; tauto
  have e_ab_bd : s(a, b) ≠ s(b, d) := by rw [Ne, Sym2.eq_iff]; tauto
  have e_ad_bd : s(a, d) ≠ s(b, d) := by rw [Ne, Sym2.eq_iff]; tauto
  -- edges of `G` avoiding the triangle are edges of `isoA G a`
  have hiso : ∀ x y, G.Adj x y → s(x, y) ≠ s(a, b) → s(x, y) ≠ s(a, d) → (isoA G a).Adj x y := by
    intro x y hxy h1 h2
    refine ⟨hxy, fun hx => ?_, fun hy => ?_⟩
    · subst hx
      rcases hN y hxy with rfl | rfl
      · exact h1 rfl
      · exact h2 rfl
    · subst hy
      rcases hN x hxy.symm with rfl | rfl
      · exact h1 (Sym2.eq_swap)
      · exact h2 (Sym2.eq_swap)
  have hBl : Bl (isoA G a) := by
    intro x y hxy
    by_cases hb : s(x, y) = s(b, d)
    · rcases Sym2.eq_iff.mp hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨ψ₀, hψ₀, hne₀⟩
      · refine ⟨ψ₀, hψ₀, ?_⟩
        rw [hψ₀.1, neg_ne_zero]
        exact hne₀
    obtain ⟨ψ, hψ, hne⟩ := hG x y hxy.1
    have hsum : ψ a b + ψ a d = 0 := by
      rw [← hψ.2.2 a, Finset.sum_eq_add b d hbd' (fun c _ hc => hψ.2.1 a c fun h' => by
        rcases hN c h' with rfl | rfl
        · exact hc.1 rfl
        · exact hc.2 rfl) (by simp) (by simp)]
    have hadb : ψ a d = ψ a b := by
      rw [← neg_eq_of_add_self zmod2_add_self (ψ a b)]
      exact (neg_eq_of_add_eq_zero_right hsum).symm
    refine ⟨_, (hψ.add (isFl_tri hab had hbd (ψ a b) (zmod2_add_self _))).restrict
      fun u v huv hn => ?_, ?_⟩
    · -- `huv` is an edge at `a`
      have key : ∀ w, G.Adj a w → ψ a w + tri a b d (ψ a b) a w = 0 := by
        intro w hw
        rcases hN w hw with rfl | rfl
        · rw [tri, ite_eq_left rfl, ite_eq_right e_ab_ad, ite_eq_right e_ab_bd, add_zero, add_zero,
            zmod2_add_self]
        · rw [tri, ite_eq_right e_ab_ad.symm, ite_eq_left rfl, ite_eq_right e_ad_bd, zero_add,
            add_zero, hadb,
            zmod2_add_self]
      have hua : u = a ∨ v = a := by
        by_contra h'
        push Not at h'
        exact hn ⟨huv, h'.1, h'.2⟩
      rcases hua with hu | hv
      · rw [hu]; exact key v (hu ▸ huv)
      · rw [hv]
        have h1 := key u (hv ▸ huv).symm
        rw [hψ.1, show tri a b d (ψ a b) a u = tri a b d (ψ a b) u a by
          simp only [tri, Sym2.eq_swap (a := a)]] at h1
        rw [← neg_eq_of_add_self zmod2_add_self (ψ u a)]
        exact h1
    · change ψ x y + tri a b d (ψ a b) x y ≠ 0
      rw [tri_eq_zero _ (fun h => ?_) (fun h => ?_) hb, add_zero]
      · exact hne
      · rcases Sym2.eq_iff.mp h with ⟨h, -⟩ | ⟨-, h⟩
        · exact hxy.2.1 h
        · exact hxy.2.2 h
      · rcases Sym2.eq_iff.mp h with ⟨h, -⟩ | ⟨-, h⟩
        · exact hxy.2.1 h
        · exact hxy.2.2 h
  obtain ⟨ℓ', hℓ', hn'⟩ := IH _ (ncard_lt_of_le (isoA_le G a) hab fun h => h.2.1 rfl) hBl
  let α : M3 := if ℓ' b d = e0 then e1 else e0
  have hα0 : α ≠ 0 := by
    simp only [α]; split_ifs
    · exact e1_ne_zero
    · exact e0_ne_zero
  have hαbd : ℓ' b d ≠ α := by
    simp only [α]; split_ifs with h
    · rw [h]; exact e0_ne_e1
    · exact h
  refine ⟨_, (hℓ'.mono (isoA_le G a)).add (isFl_tri hab had hbd α (m3_add_self _)),
    fun x y hxy => ?_⟩
  have hl0 : ∀ x y, s(x, y) = s(a, b) ∨ s(x, y) = s(a, d) → ℓ' x y = 0 := by
    intro x y hxy'
    apply hℓ'.2.1
    rintro ⟨-, hx, hy⟩
    rcases hxy' with h' | h' <;> rcases Sym2.eq_iff.mp h' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp_all
  change ℓ' x y + tri a b d α x y ≠ 0
  by_cases h1 : s(x, y) = s(a, b)
  · rw [hl0 x y (Or.inl h1), zero_add, tri, ite_eq_left h1, ite_eq_right (h1 ▸ e_ab_ad),
      ite_eq_right (h1 ▸ e_ab_bd), add_zero, add_zero]
    exact hα0
  by_cases h2 : s(x, y) = s(a, d)
  · rw [hl0 x y (Or.inr h2), zero_add, tri, ite_eq_right (h2 ▸ e_ab_ad.symm), ite_eq_left h2,
      ite_eq_right (h2 ▸ e_ad_bd), zero_add, add_zero]
    exact hα0
  by_cases h3 : s(x, y) = s(b, d)
  · rw [tri, ite_eq_right h1, ite_eq_right h2, ite_eq_left h3, zero_add, zero_add]
    have : ℓ' x y = ℓ' b d := by
      rcases Sym2.eq_iff.mp h3 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · rw [hℓ'.1, neg_eq_of_add_self m3_add_self]
    rw [this]
    intro h0
    apply hαbd
    rw [← neg_eq_of_add_self m3_add_self α]
    exact eq_neg_of_add_eq_zero_left h0
  · rw [tri_eq_zero _ h1 h2 h3, add_zero]
    exact hn' x y (hiso x y hxy h1 h2)

end EightFlow
