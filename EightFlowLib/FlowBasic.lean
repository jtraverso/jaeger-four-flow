/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import JaegerLib.Jaeger

/-!
# Flows given by functions on ordered pairs of vertices

Auxiliary material for Jaeger's 8-flow theorem: flows `V → V → M`, the cut condition, the
flow of a cycle, and cuts given by bridges.
-/

@[expose] public section

open Finset SimpleGraph

attribute [local instance low] Classical.propDecidable

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace EightFlow

variable {V : Type*} [Fintype V]

/-- `f` is a flow on `G` with values in `M`: antisymmetric, supported on the edges of `G` and
conserved at every vertex. -/
def IsFl {M : Type*} [AddCommGroup M] (G : SimpleGraph V) (f : V → V → M) : Prop :=
  (∀ u v, f v u = -f u v) ∧ (∀ u v, ¬ G.Adj u v → f u v = 0) ∧ ∀ v, ∑ w, f v w = 0

/-- The group `ℤ₂³`. -/
abbrev M3 := Fin 3 → ZMod 2

/-- Every edge of `G` carries a nonzero value of some `ℤ₂`-flow. -/
def Bl (G : SimpleGraph V) : Prop :=
  ∀ u v, G.Adj u v → ∃ f : V → V → ZMod 2, IsFl G f ∧ f u v ≠ 0

/-- `G` has a nowhere-zero `ℤ₂³`-flow. -/
def Gl (G : SimpleGraph V) : Prop :=
  ∃ f : V → V → M3, IsFl G f ∧ ∀ u v, G.Adj u v → f u v ≠ 0

lemma zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  fin_cases x <;> decide

lemma m3_add_self (x : M3) : x + x = 0 := by
  funext i
  exact zmod2_add_self _

lemma neg_eq_of_add_self {M : Type*} [AddCommGroup M] (h2 : ∀ x : M, x + x = 0) (x : M) :
    -x = x := by
  rw [neg_eq_iff_add_eq_zero, h2]

variable {M : Type*} [AddCommGroup M]

lemma IsFl.add {G : SimpleGraph V} {f g : V → V → M} (hf : IsFl G f) (hg : IsFl G g) :
    IsFl G (fun u v => f u v + g u v) := by
  refine ⟨fun u v => ?_, fun u v h => ?_, fun v => ?_⟩
  · simp only; rw [hf.1, hg.1, neg_add]
  · simp only; rw [hf.2.1 u v h, hg.2.1 u v h, add_zero]
  · simp only; rw [sum_add_distrib, hf.2.2, hg.2.2, add_zero]

lemma IsFl.sub {G : SimpleGraph V} {f g : V → V → M} (hf : IsFl G f) (hg : IsFl G g) :
    IsFl G (fun u v => f u v - g u v) := by
  refine ⟨fun u v => ?_, fun u v h => ?_, fun v => ?_⟩
  · simp only; rw [hf.1, hg.1]; abel
  · simp only; rw [hf.2.1 u v h, hg.2.1 u v h, sub_zero]
  · simp only; rw [sum_sub_distrib, hf.2.2, hg.2.2, sub_zero]

lemma IsFl.mono {G G' : SimpleGraph V} {f : V → V → M} (hf : IsFl G f) (h : G ≤ G') :
    IsFl G' f :=
  ⟨hf.1, fun u v huv => hf.2.1 u v fun h' => huv (h h'), hf.2.2⟩

lemma IsFl.diag {G : SimpleGraph V} {f : V → V → M} (hf : IsFl G f) (v : V) : f v v = 0 :=
  hf.2.1 v v (G.irrefl)

omit [Fintype V] in
/-- An antisymmetric function vanishing on the diagonal sums to zero over a block `T × T`. -/
lemma sum_block_eq_zero {f : V → V → M} (ha : ∀ u v, f v u = -f u v) (hd : ∀ v, f v v = 0)
    (T : Finset V) : ∑ x ∈ T, ∑ y ∈ T, f x y = 0 := by
  rw [← Finset.sum_product']
  refine Finset.sum_involution (fun p _ => p.swap) ?_ ?_ ?_ ?_
  · intro p _
    simp [ha p.1 p.2]
  · intro p _ hp h
    apply hp
    have : p.1 = p.2 := congrArg Prod.fst h |>.symm
    rw [this, hd]
  · intro p hp
    simp only [mem_product, Prod.fst_swap, Prod.snd_swap] at hp ⊢
    exact ⟨hp.2, hp.1⟩
  · intro p _
    rfl

/-- **Cut condition.** The total value of a flow leaving a set of vertices is zero. -/
lemma cut_sum {G : SimpleGraph V} {f : V → V → M} (hf : IsFl G f) (S : Finset V) :
    ∑ x ∈ S, ∑ y ∈ Sᶜ, f x y = 0 := by
  have h1 : ∑ x ∈ S, ∑ y, f x y = 0 := sum_eq_zero fun x _ => hf.2.2 x
  have h2 : ∀ x, ∑ y, f x y = ∑ y ∈ S, f x y + ∑ y ∈ Sᶜ, f x y :=
    fun x => (sum_add_sum_compl S _).symm
  simp_rw [h2, sum_add_distrib] at h1
  rwa [sum_block_eq_zero hf.1 hf.diag, zero_add] at h1

/-- The ordered pairs `(x, y)` of adjacent vertices with `x ∈ S`, `y ∉ S`. -/
noncomputable def X (G : SimpleGraph V) (S : Finset V) : Finset (V × V) :=
  (S ×ˢ Sᶜ).filter fun p => G.Adj p.1 p.2

lemma mem_X {G : SimpleGraph V} {S : Finset V} {p : V × V} :
    p ∈ X G S ↔ p.1 ∈ S ∧ p.2 ∉ S ∧ G.Adj p.1 p.2 := by
  simp [X, and_assoc]

lemma cut_sum_X {G : SimpleGraph V} {f : V → V → M} (hf : IsFl G f) (S : Finset V) :
    ∑ p ∈ X G S, f p.1 p.2 = 0 := by
  rw [← cut_sum hf S, ← Finset.sum_product', X, Finset.sum_filter_of_ne]
  intro p _ hp
  by_contra h
  exact hp (hf.2.1 _ _ h)

/-- The pairs crossing the complement are the reversed pairs. -/
lemma X_compl (G : SimpleGraph V) (S : Finset V) :
    X G Sᶜ = (X G S).image Prod.swap := by
  ext ⟨x, y⟩
  simp only [mem_image, mem_X, Prod.exists, Prod.swap_prod_mk, Prod.mk.injEq]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨y, x, ⟨by simpa using h2, by simpa using h1, h3.symm⟩, rfl, rfl⟩
  · rintro ⟨a, b, ⟨h1, h2, h3⟩, rfl, rfl⟩
    exact ⟨by simpa using h2, by simpa using h1, h3.symm⟩

/-- A bridge-free edge: a cycle through `s(b, d)` gives a `ℤ₂`-flow nonzero on it. -/
lemma cycle_flow {G : SimpleGraph V} {b d : V} (hbd : G.Adj b d)
    (hr : (G.deleteEdges {s(b, d)}).Reachable b d) :
    ∃ ψ : V → V → ZMod 2, IsFl G ψ ∧ ψ b d ≠ 0 := by
  obtain ⟨p, hp⟩ := hr.exists_isPath
  let q : G.Walk b d := p.mapLe (G.deleteEdges_le _)
  have hq : q.IsPath := hp.mapLe _
  have hqe : q.edges = p.edges := Walk.edges_mapLe_eq_edges _ _
  let c : G.Walk d d := Walk.cons hbd.symm q
  have hc : c.IsCycle := by
    rw [Walk.cons_isCycle_iff]
    refine ⟨hq, fun h => ?_⟩
    rw [hqe] at h
    have := p.edges_subset_edgeSet h
    rw [edgeSet_deleteEdges] at this
    exact this.2 (by simp [Sym2.eq_swap])
  have htr : c.IsTrail := hc.isCircuit.isTrail
  refine ⟨fun x y => if s(x, y) ∈ c.edges then 1 else 0, ⟨fun u v => ?_, fun u v h => ?_,
    fun v => ?_⟩, ?_⟩
  · simp only [Sym2.eq_swap (a := v)]
    split_ifs <;> decide
  · simp only
    split_ifs with h'
    · exact absurd (c.adj_of_mem_edges h') h
    · rfl
  · let A : SimpleGraph V := fromEdgeSet {e | e ∈ c.edges}
    have hA : ∀ w, (if s(v, w) ∈ c.edges then (1 : ZMod 2) else 0) =
        if A.Adj v w then 1 else 0 := by
      intro w
      have : A.Adj v w ↔ s(v, w) ∈ c.edges := by
        simp only [A, fromEdgeSet_adj, Set.mem_ofPred_eq, and_iff_left_iff_imp]
        exact fun h => (c.adj_of_mem_edges h).ne
      simp only [this]
    simp only [hA]
    suffices key : (A.degree v : ZMod 2) = 0 by
      rw [Jaeger.degree_cast_zmod] at key
      convert key
    rw [ZMod.natCast_eq_zero_iff_even, ← card_incidenceFinset_eq_degree]
    have hinc : A.incidenceFinset v = c.edges.toFinset.filter (fun e => v ∈ e) := by
      ext e
      rw [mem_incidenceFinset, Finset.mem_filter, List.mem_toFinset]
      simp only [incidenceSet, A, edgeSet_fromEdgeSet]
      change (e ∈ _ ∧ _) ↔ _
      rw [Set.mem_sdiff]
      constructor
      · rintro ⟨⟨h1, -⟩, h2⟩
        exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨h1, G.not_isDiag_of_mem_edgeSet (c.edges_subset_edgeSet h1)⟩, h2⟩
    rw [hinc, SimpleGraph.card_filter_toFinset_of_nodup htr.edges_nodup]
    exact (htr.even_countP_edges_iff v).mpr fun h => absurd rfl h
  · simp only [c, Walk.edges_cons, List.mem_cons, Sym2.eq_swap, true_or, ite_true]
    decide

/-- If no `ℤ₂`-flow is nonzero on the edge `s(b, d)`, then it is the only edge leaving some
set containing `b` but not `d`. -/
lemma bridge_cut {G : SimpleGraph V} {b d : V} (hbd : G.Adj b d)
    (h : ¬ ∃ ψ : V → V → ZMod 2, IsFl G ψ ∧ ψ b d ≠ 0) :
    ∃ R : Finset V, b ∈ R ∧ d ∉ R ∧ ∀ x y, x ∈ R → y ∉ R → G.Adj x y → x = b ∧ y = d := by
  have hnr : ¬ (G.deleteEdges {s(b, d)}).Reachable b d := fun hr => h (cycle_flow hbd hr)
  refine ⟨univ.filter fun w => (G.deleteEdges {s(b, d)}).Reachable b w, by simp, by simpa using hnr,
    fun x y hx hy hxy => ?_⟩
  simp only [mem_filter, mem_univ, true_and] at hx hy
  by_cases he : s(x, y) = s(b, d)
  · rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
    · exact absurd hx hnr
  · exfalso
    apply hy
    refine hx.trans (Adj.reachable ?_)
    rw [deleteEdges_adj]
    exact ⟨hxy, by simpa using he⟩

/-- A cut with a single crossing pair contradicts `Bl`. -/
lemma X_card_ne_one {G : SimpleGraph V} (hG : Bl G) (S : Finset V) : (X G S).card ≠ 1 := by
  intro h
  obtain ⟨⟨x, y⟩, hp⟩ := Finset.card_eq_one.mp h
  have hm : (x, y) ∈ X G S := by rw [hp]; exact mem_singleton_self _
  obtain ⟨ψ, hψ, hne⟩ := hG x y (mem_X.mp hm).2.2
  have := cut_sum_X hψ S
  rw [hp, sum_singleton] at this
  exact hne this

/-- A bridgeless graph (in Mathlib's sense) satisfies `Bl`. -/
lemma bl_of_bridgeless {G : SimpleGraph V} (hG : ∀ e ∈ G.edgeSet, ¬ G.IsBridge e) : Bl G := by
  intro u v huv
  have := hG s(u, v) huv
  rw [isBridge_iff, not_not] at this
  exact cycle_flow huv this

end EightFlow
