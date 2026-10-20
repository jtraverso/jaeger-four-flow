/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# Finite multigraphs and group-valued flows

Auxiliary material for Seymour's 6-flow theorem. A multigraph is given by a finite set of active
edges together with a tail and a head for every edge (loops and parallel edges are allowed).
For a function `f` on the edges with values in an abelian group, `bd f v` is the net inflow of
`f` at `v`; `f` is a flow when `bd f = 0`.
-/

@[expose] public section

open Finset SimpleGraph

attribute [local instance low] Classical.propDecidable

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace SixFlow

/-- A finite multigraph with oriented edges: a finite set of active edges, a tail and a head. -/
structure MG (V E : Type*) where
  /-- The active edges. -/
  act : Finset E
  /-- The tail of an edge. -/
  src : E → V
  /-- The head of an edge. -/
  tgt : E → V

namespace MG

variable {V E : Type*} [Fintype V] {A : Type*} [AddCommGroup A] (M : MG V E)

/-- Net inflow of `f` at `v`. -/
noncomputable def bd (f : E → A) (v : V) : A :=
  ∑ e ∈ M.act, ((if M.tgt e = v then f e else 0) - (if M.src e = v then f e else 0))

/-- The active edges with both ends in `T`. -/
noncomputable def ins (T : Finset V) : Finset E :=
  M.act.filter fun e => M.src e ∈ T ∧ M.tgt e ∈ T

/-- The active edges crossing `S`. -/
noncomputable def cut (S : Finset V) : Finset E :=
  M.act.filter fun e => (M.src e ∈ S ∧ M.tgt e ∉ S) ∨ (M.src e ∉ S ∧ M.tgt e ∈ S)

/-- The indicator function of `F` with value `a`. -/
noncomputable def ind (F : Finset E) (a : A) : E → A := fun e => if e ∈ F then a else 0

/-- `F` is an even edge set: its indicator is a `ℤ₂`-flow. -/
def Ev (F : Finset E) : Prop := M.bd (ind F (1 : ZMod 2)) = 0

/-- The simple graph underlying a set of edges. -/
def shadow (Q : Finset E) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet {z | ∃ e ∈ Q, s(M.src e, M.tgt e) = z}

/-- `Q` lies inside `W` and connects all the vertices of `W`. -/
def Conn (Q : Finset E) (W : Finset V) : Prop :=
  Q ⊆ M.ins W ∧ ∀ a ∈ W, ∀ b ∈ W, (M.shadow Q).Reachable a b

variable {M}

lemma mem_ins {T : Finset V} {e : E} : e ∈ M.ins T ↔ e ∈ M.act ∧ M.src e ∈ T ∧ M.tgt e ∈ T := by
  simp [ins]

lemma ins_subset (T : Finset V) : M.ins T ⊆ M.act := filter_subset _ _

lemma ins_mono {T T' : Finset V} (h : T ⊆ T') : M.ins T ⊆ M.ins T' := by
  intro e he
  rw [mem_ins] at he ⊢
  exact ⟨he.1, h he.2.1, h he.2.2⟩

lemma mem_cut {S : Finset V} {e : E} :
    e ∈ M.cut S ↔ e ∈ M.act ∧ ((M.src e ∈ S ∧ M.tgt e ∉ S) ∨ (M.src e ∉ S ∧ M.tgt e ∈ S)) := by
  simp [cut]

lemma shadow_adj {Q : Finset E} {a b : V} :
    (M.shadow Q).Adj a b ↔ (∃ e ∈ Q, s(M.src e, M.tgt e) = s(a, b)) ∧ a ≠ b := by
  simp [shadow, fromEdgeSet_adj]

lemma shadow_mono {Q Q' : Finset E} (h : Q ⊆ Q') : M.shadow Q ≤ M.shadow Q' := by
  intro a b hab
  rw [shadow_adj] at hab ⊢
  obtain ⟨⟨e, he, he'⟩, hne⟩ := hab
  exact ⟨⟨e, h he, he'⟩, hne⟩

lemma ind_apply (F : Finset E) (a : A) (e : E) : ind F a e = if e ∈ F then a else 0 := rfl

lemma bd_congr {f g : E → A} (h : ∀ e ∈ M.act, f e = g e) : M.bd f = M.bd g := by
  funext v
  exact sum_congr rfl fun e he => by rw [h e he]

lemma bd_add (f g : E → A) : M.bd (f + g) = M.bd f + M.bd g := by
  funext v
  simp only [bd, Pi.add_apply, ← sum_add_distrib]
  refine sum_congr rfl fun e _ => ?_
  split_ifs <;> abel

lemma bd_add' (f g : E → A) : M.bd (fun e => f e + g e) = M.bd f + M.bd g := bd_add f g

lemma bd_neg (f : E → A) : M.bd (-f) = -M.bd f := by
  funext v
  simp only [bd, Pi.neg_apply, ← sum_neg_distrib]
  refine sum_congr rfl fun e _ => ?_
  split_ifs <;> abel

lemma bd_sub (f g : E → A) : M.bd (f - g) = M.bd f - M.bd g := by
  rw [sub_eq_add_neg, bd_add, bd_neg, ← sub_eq_add_neg]

lemma bd_zero : M.bd (0 : E → A) = 0 := by
  funext v
  simp [bd]

lemma bd_zsmul (h : E → ℤ) (c : A) (v : V) : M.bd (fun e => h e • c) v = M.bd h v • c := by
  simp only [bd, sum_smul, sub_smul, ite_smul, zero_smul]

lemma bd_sum {ι : Type*} (s : Finset ι) (f : ι → E → A) (v : V) :
    M.bd (fun e => ∑ i ∈ s, f i e) v = ∑ i ∈ s, M.bd (f i) v := by
  simp only [bd]
  rw [sum_comm]
  refine sum_congr rfl fun e _ => ?_
  rw [sum_sub_distrib]
  split_ifs <;> simp

/-- The total net inflow vanishes. -/
lemma sum_bd (f : E → A) : ∑ v, M.bd f v = 0 := by
  simp only [bd]
  rw [sum_comm]
  refine sum_eq_zero fun e _ => ?_
  rw [sum_sub_distrib]
  simp

/-- The net inflow into a set is computed from the edges. -/
lemma sum_bd_set (f : E → A) (S : Finset V) :
    ∑ v ∈ S, M.bd f v =
      ∑ e ∈ M.act, ((if M.tgt e ∈ S then f e else 0) - (if M.src e ∈ S then f e else 0)) := by
  simp only [bd]
  rw [sum_comm]
  refine sum_congr rfl fun e _ => ?_
  rw [sum_sub_distrib]
  simp [Finset.sum_ite_eq']

/-- The net inflow into a set only involves the crossing edges. -/
lemma sum_bd_set_cut (f : E → A) (S : Finset V) :
    ∑ v ∈ S, M.bd f v =
      ∑ e ∈ M.cut S, ((if M.tgt e ∈ S then f e else 0) - (if M.src e ∈ S then f e else 0)) := by
  rw [sum_bd_set, cut, sum_filter]
  refine sum_congr rfl fun e _ => ?_
  split_ifs <;> simp_all

lemma bd_eq_zero_of_supp {f : E → A} {T : Finset V} (hf : ∀ e, e ∉ M.ins T → f e = 0)
    {v : V} (hv : v ∉ T) : M.bd f v = 0 := by
  refine sum_eq_zero fun e he => ?_
  by_cases hin : e ∈ M.ins T
  · rw [mem_ins] at hin
    have h1 : M.tgt e ≠ v := fun h => hv (h ▸ hin.2.2)
    have h2 : M.src e ≠ v := fun h => hv (h ▸ hin.2.1)
    simp [h1, h2]
  · simp [hf e hin]

lemma bd_ind_single {e : E} (he : e ∈ M.act) (a : A) (v : V) :
    M.bd (ind {e} a) v = (if M.tgt e = v then a else 0) - (if M.src e = v then a else 0) := by
  rw [bd, Finset.sum_eq_single_of_mem e he]
  · simp [ind]
  · intro b _ hb
    simp [ind, hb]

lemma ind_union {F G : Finset E} (h : Disjoint F G) (a : A) :
    ind (F ∪ G) a = ind F a + ind G a := by
  funext e
  simp only [ind, Pi.add_apply, mem_union]
  by_cases hF : e ∈ F
  · have hG : e ∉ G := disjoint_left.mp h hF
    simp [hF, hG]
  · simp [hF]

lemma ind_sdiff {F G : Finset E} (h : G ⊆ F) (a : A) :
    ind (F \ G) a = ind F a - ind G a := by
  funext e
  simp only [ind, Pi.sub_apply, mem_sdiff]
  by_cases hG : e ∈ G
  · simp [hG, h hG]
  · simp [hG]

lemma zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  fin_cases x <;> rfl

lemma zmod2_neg (x : ZMod 2) : -x = x := by
  fin_cases x <;> rfl

lemma zmod2_sub (x y : ZMod 2) : x - y = x + y := by
  rw [sub_eq_add_neg, zmod2_neg]

lemma Ev.union {F G : Finset E} (hF : M.Ev F) (hG : M.Ev G) (h : Disjoint F G) :
    M.Ev (F ∪ G) := by
  unfold Ev at *
  rw [ind_union h, bd_add, hF, hG, add_zero]

lemma Ev.empty : M.Ev (∅ : Finset E) := by
  unfold Ev
  rw [show ind (∅ : Finset E) (1 : ZMod 2) = 0 from funext fun e => by simp [ind], bd_zero]

/-! ### Reachability in shadows -/

lemma mem_of_reachable {Q : Finset E} {T : Finset V} (hQ : Q ⊆ M.ins T) {a b : V}
    (ha : a ∈ T) (h : (M.shadow Q).Reachable a b) : b ∈ T := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact ha
  | cons hadj p ih =>
    apply ih
    rw [shadow_adj] at hadj
    obtain ⟨⟨e, he, he'⟩, -⟩ := hadj
    have := mem_ins.mp (hQ he)
    rcases Sym2.eq_iff.mp he' with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact h2 ▸ this.2.2
    · exact h1 ▸ this.2.1

lemma support_subset_of_ins {Q : Finset E} {T : Finset V} (hQ : Q ⊆ M.ins T) {a b : V}
    (ha : a ∈ T) (p : (M.shadow Q).Walk a b) : ∀ v ∈ p.support, v ∈ T := by
  intro v hv
  exact mem_of_reachable hQ ha ⟨p.takeUntil v hv⟩

/-- An edge of `Q` makes its ends adjacent or equal in the shadow of `Q`. -/
lemma reachable_of_mem {Q : Finset E} {e : E} (he : e ∈ Q) :
    (M.shadow Q).Reachable (M.src e) (M.tgt e) := by
  by_cases h : M.src e = M.tgt e
  · rw [h]
  · exact Adj.reachable (shadow_adj.mpr ⟨⟨e, he, rfl⟩, h⟩)

lemma Conn.mono_edges {Q Q' : Finset E} {W : Finset V} (h : M.Conn Q W) (hQ : Q ⊆ Q')
    (hQ' : Q' ⊆ M.ins W) : M.Conn Q' W :=
  ⟨hQ', fun a ha b hb => (h.2 a ha b hb).mono (shadow_mono hQ)⟩

lemma Conn.union {Q Q' : Finset E} {W W' : Finset V} (h : M.Conn Q W) (h' : M.Conn Q' W')
    {c : V} (hc : c ∈ W) (hc' : c ∈ W') : M.Conn (Q ∪ Q') (W ∪ W') := by
  refine ⟨union_subset (h.1.trans (ins_mono subset_union_left))
    (h'.1.trans (ins_mono subset_union_right)), ?_⟩
  have key : ∀ a ∈ W ∪ W', (M.shadow (Q ∪ Q')).Reachable a c := by
    intro a ha
    rcases mem_union.mp ha with ha | ha
    · exact (h.2 a ha c hc).mono (shadow_mono subset_union_left)
    · exact (h'.2 a ha c hc').mono (shadow_mono subset_union_right)
  intro a ha b hb
  exact (key a ha).trans (key b hb).symm

lemma Conn.single {e : E} (he : e ∈ M.act) : M.Conn {e} {M.src e, M.tgt e} := by
  refine ⟨fun x hx => ?_, ?_⟩
  · rw [mem_singleton] at hx
    subst hx
    exact mem_ins.mpr ⟨he, by simp, by simp⟩
  · have h := reachable_of_mem (M := M) (mem_singleton_self e)
    intro a ha b hb
    simp only [mem_insert, mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · rfl
    · exact h
    · exact h.symm
    · rfl

lemma Conn.singleton_empty (x : V) : M.Conn (∅ : Finset E) {x} := by
  refine ⟨empty_subset _, fun a ha b hb => ?_⟩
  rw [mem_singleton] at ha hb
  rw [ha, hb]

/-! ### Routing along connected edge sets -/

/-- A walk in the shadow of `Q` carries an integer function supported on `Q` sending one unit
from its start to its end. -/
lemma walk_flow {Q : Finset E} (hQ : Q ⊆ M.act) {a b : V} (p : (M.shadow Q).Walk a b) :
    ∃ h : E → ℤ, (∀ e, e ∉ Q → h e = 0) ∧
      ∀ v, M.bd h v = (if v = b then 1 else 0) - (if v = a then 1 else 0) := by
  induction p with
  | nil => exact ⟨0, fun _ _ => rfl, fun v => by simp [bd]⟩
  | @cons a c b hadj p ih =>
    obtain ⟨h, hs, hb⟩ := ih
    rw [shadow_adj] at hadj
    obtain ⟨⟨e, he, he'⟩, hne⟩ := hadj
    have heA := hQ he
    rcases Sym2.eq_iff.mp he' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine ⟨h + ind {e} 1, fun e' he'' => ?_, fun v => ?_⟩
      · have : e' ≠ e := fun h => he'' (h ▸ he)
        simp [hs e' he'', ind, this]
      · rw [bd_add, Pi.add_apply, hb, bd_ind_single heA, h1, h2]
        by_cases hva : v = a <;> by_cases hvc : v = c <;> by_cases hvb : v = b <;>
          simp_all [eq_comm]
    · refine ⟨h - ind {e} 1, fun e' he'' => ?_, fun v => ?_⟩
      · have : e' ≠ e := fun h => he'' (h ▸ he)
        simp [hs e' he'', ind, this]
      · rw [bd_sub, Pi.sub_apply, hb, bd_ind_single heA, h1, h2]
        by_cases hva : v = a <;> by_cases hvc : v = c <;> by_cases hvb : v = b <;>
          simp_all [eq_comm]

/-- **Routing.** If `Q` connects `W`, every demand on `W` with total zero is the net inflow of a
function supported on `Q`. -/
lemma Conn.route {Q : Finset E} {W : Finset V} (hC : M.Conn Q W) (β : V → A)
    (hβ : ∀ v, v ∉ W → β v = 0) (hsum : ∑ v, β v = 0) :
    ∃ h : E → A, (∀ e, e ∉ Q → h e = 0) ∧ M.bd h = β := by
  rcases W.eq_empty_or_nonempty with hW | ⟨w₀, hw₀⟩
  · refine ⟨0, fun _ _ => rfl, ?_⟩
    rw [bd_zero]
    funext v
    rw [hβ v (by simp [hW])]
    rfl
  have hQ : Q ⊆ M.act := hC.1.trans (ins_subset W)
  have key : ∀ v ∈ W, ∃ h : E → ℤ, (∀ e, e ∉ Q → h e = 0) ∧
      ∀ u, M.bd h u = (if u = w₀ then 1 else 0) - (if u = v then 1 else 0) := by
    intro v hv
    obtain ⟨p⟩ := hC.2 v hv w₀ hw₀
    exact walk_flow hQ p
  choose! H hHs hHb using key
  refine ⟨fun e => ∑ v ∈ W, H v e • (-β v), fun e he => ?_, ?_⟩
  · exact sum_eq_zero fun v hv => by rw [hHs v hv e he, zero_smul]
  · funext u
    rw [bd_sum]
    simp only [bd_zsmul]
    rw [sum_congr rfl fun v hv => by rw [hHb v hv u]]
    simp only [sub_smul, ite_smul, one_smul, zero_smul, sum_sub_distrib]
    rw [sum_ite_eq]
    have hs : ∑ v ∈ W, β v = 0 := by
      rw [← hsum]
      exact (sum_subset (subset_univ W) fun v _ hv => hβ v hv)
    have h1 : (∑ x ∈ W, if u = w₀ then -β x else 0) = 0 := by
      split_ifs
      · rw [sum_neg_distrib, hs, neg_zero]
      · simp
    rw [h1, zero_sub]
    by_cases hu : u ∈ W
    · simp [hu]
    · simp [hu, hβ u hu]

/-- A path in the shadow of `Q` gives a set of edges of `Q` connecting its support, whose
indicator has odd degree exactly at the two ends. -/
lemma path_edges {Q : Finset E} (hQ : Q ⊆ M.act) {a b : V} (p : (M.shadow Q).Walk a b)
    (hp : p.IsPath) : ∃ P W, P ⊆ Q ∧ W ⊆ p.support.toFinset ∧ a ∈ W ∧ b ∈ W ∧ M.Conn P W ∧
      M.bd (ind P (1 : ZMod 2)) = fun v => (if v = a then 1 else 0) + (if v = b then 1 else 0) := by
  induction p with
  | nil =>
    refine ⟨∅, {_}, empty_subset _, by simp, mem_singleton_self _, mem_singleton_self _,
      Conn.singleton_empty _, ?_⟩
    rw [show ind (∅ : Finset E) (1 : ZMod 2) = 0 from funext fun e => by simp [ind], bd_zero]
    funext v
    simp only [Pi.zero_apply]
    split_ifs <;> decide
  | @cons a c b hadj p ih =>
    rw [Walk.cons_isPath_iff] at hp
    obtain ⟨P, W, hPQ, hW, hcW, hbW, hC, hbd⟩ := ih hp.1
    have hadj' := hadj
    rw [shadow_adj] at hadj
    obtain ⟨⟨e, he, he'⟩, hne⟩ := hadj
    have heA := hQ he
    have hends : (M.src e = a ∧ M.tgt e = c) ∨ (M.src e = c ∧ M.tgt e = a) := by
      rcases Sym2.eq_iff.mp he' with h | h
      · exact Or.inl h
      · exact Or.inr h
    have haW : a ∉ W := fun h => hp.2 (by simpa using hW h)
    have heP : e ∉ P := by
      intro h
      have := mem_ins.mp (hC.1 h)
      rcases hends with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact haW (h1 ▸ this.2.1)
      · exact haW (h2 ▸ this.2.2)
    refine ⟨insert e P, insert a W, insert_subset he hPQ, ?_, mem_insert_self _ _,
      mem_insert_of_mem hbW, ?_, ?_⟩
    · intro v hv
      rw [mem_insert] at hv
      rcases hv with rfl | hv
      · simp
      · have := hW hv
        simp only [List.mem_toFinset, Walk.support_cons, List.mem_cons] at this ⊢
        exact Or.inr this
    · have hC1 : M.Conn {e} {M.src e, M.tgt e} := Conn.single heA
      have hcE : c ∈ ({M.src e, M.tgt e} : Finset V) := by
        rcases hends with ⟨-, h⟩ | ⟨h, -⟩ <;> simp [h]
      have := hC1.union hC hcE hcW
      have hpair : ({M.src e, M.tgt e} : Finset V) = {a, c} := by
        rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
        exact pair_comm c a
      have hset : ({M.src e, M.tgt e} : Finset V) ∪ W = insert a W := by
        rw [hpair]
        ext v
        simp only [mem_union, mem_insert, mem_singleton]
        constructor
        · rintro ((rfl | rfl) | h)
          exacts [Or.inl rfl, Or.inr hcW, Or.inr h]
        · rintro (rfl | h)
          exacts [Or.inl (Or.inl rfl), Or.inr h]
      rw [← hset, insert_eq]
      exact this
    · rw [insert_eq, ind_union (disjoint_singleton_left.mpr heP), bd_add, hbd]
      funext v
      rw [Pi.add_apply, bd_ind_single heA]
      rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;>
        by_cases hva : v = a <;> by_cases hvc : v = c <;> by_cases hvb : v = b <;>
        simp_all [eq_comm] <;> decide

end MG

end SixFlow
