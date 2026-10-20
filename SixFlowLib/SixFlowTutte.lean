/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# Lifting `ℤ/k`-flows to integer flows (Tutte)

Among the integer lifts of a nowhere-zero `ℤ/k`-flow with values in `(−k, k)` we choose one with
minimal total excess. An augmenting path argument shows that the minimum is zero.
-/

@[expose] public section

open Finset SimpleGraph

attribute [local instance low] Classical.propDecidable

namespace SixFlow

namespace Tutte

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The excess (net outflow) of `ψ` at `v`. -/
noncomputable def ex (ψ : G.Dart → ℤ) (v : V) : ℤ := ∑ d ∈ univ.filter (fun d : G.Dart ↦ d.fst = v), ψ d

lemma sum_filter_symm {M : Type*} [AddCommMonoid M] (f : G.Dart → M) (v : V) :
    ∑ d ∈ univ.filter (fun d : G.Dart ↦ d.fst = v), f d.symm =
      ∑ d ∈ univ.filter (fun d : G.Dart ↦ d.snd = v), f d := by
  refine sum_bij' (fun d _ => d.symm) (fun d _ => d.symm) ?_ ?_ ?_ ?_ ?_ <;> simp

lemma sum_count_filter {α : Type*} [Fintype α] [DecidableEq α] (P : α → Prop) [DecidablePred P]
    (l : List α) :
    ∑ a ∈ univ.filter P, (l.count a : ℤ) = (l.countP (fun a => decide (P a)) : ℤ) := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.count_cons, List.countP_cons, Nat.cast_add, sum_add_distrib, ih]
    congr 1
    by_cases hx : P x
    · rw [sum_eq_single_of_mem x (by simp [hx])]
      · simp [hx]
      · intro b _ hb
        simp [Ne.symm hb, beq_iff_eq]
    · rw [sum_eq_zero]
      · simp [hx]
      · intro b hb
        have : x ≠ b := fun h => hx (h ▸ (mem_filter.mp hb).2)
        simp [beq_iff_eq, this]

lemma countP_darts_fst_add {u w : V} (p : G.Walk u w) (v : V) :
    (p.darts.countP (fun d => decide (d.fst = v)) : ℤ) + (if w = v then 1 else 0) =
      (p.darts.countP (fun d => decide (d.snd = v)) : ℤ) + (if u = v then 1 else 0) := by
  induction p with
  | nil => simp
  | cons h q ih =>
    rename_i a b c
    simp only [Walk.darts_cons, List.countP_cons, Nat.cast_add]
    by_cases hav : a = v <;> by_cases hbv : b = v <;> simp_all <;> omega

lemma sum_symm_eq_zero (ψ : G.Dart → ℤ) (ha : ∀ d, ψ d.symm = -ψ d) : ∑ d, ψ d = 0 := by
  have h : ∑ d, ψ d = ∑ d : G.Dart, ψ d.symm :=
    (Fintype.sum_equiv (Dart.symm_involutive.toPerm _) (fun d : G.Dart => ψ d.symm) ψ
      (fun _ => rfl)).symm
  simp only [ha, sum_neg_distrib] at h
  linarith

lemma sum_ex (ψ : G.Dart → ℤ) (ha : ∀ d, ψ d.symm = -ψ d) : ∑ v, ex ψ v = 0 := by
  unfold ex
  rw [sum_fiberwise univ (fun d : G.Dart => d.fst) ψ]
  exact sum_symm_eq_zero ψ ha

lemma sum_ex_set (ψ : G.Dart → ℤ) (ha : ∀ d, ψ d.symm = -ψ d) (R : Finset V) :
    ∑ v ∈ R, ex ψ v = ∑ d ∈ univ.filter (fun d : G.Dart ↦ d.fst ∈ R ∧ d.snd ∉ R), ψ d := by
  unfold ex
  have hR : ∀ v ∈ R, univ.filter (fun d : G.Dart => d.fst = v) =
      (univ.filter fun d : G.Dart => d.fst ∈ R).filter (fun d => d.fst = v) := by
    intro v hv
    ext d
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro rfl
      exact ⟨hv, rfl⟩
    · exact fun h => h.2
  rw [sum_congr rfl fun v hv => by rw [hR v hv]]
  rw [sum_fiberwise_of_maps_to (g := fun d : G.Dart => d.fst)
    (fun d hd => (mem_filter.mp hd).2)]
  have hsplit := sum_filter_add_sum_filter_not (univ.filter fun d : G.Dart => d.fst ∈ R)
    (fun d => d.snd ∈ R) ψ
  rw [← hsplit, filter_filter, filter_filter]
  have h0 : ∑ d ∈ univ.filter (fun d : G.Dart => d.fst ∈ R ∧ d.snd ∈ R), ψ d = 0 := by
    have h : ∑ d ∈ univ.filter (fun d : G.Dart => d.fst ∈ R ∧ d.snd ∈ R), ψ d =
        ∑ d ∈ univ.filter (fun d : G.Dart => d.fst ∈ R ∧ d.snd ∈ R), ψ d.symm := by
      refine sum_bij' (fun d _ => d.symm) (fun d _ => d.symm) ?_ ?_ ?_ ?_ ?_
      all_goals intros; simp_all [and_comm]
    simp only [ha, sum_neg_distrib] at h
    linarith
  rw [h0, zero_add]

/-- Integer lifts of `φ` with values in `(−k, k)`. -/
def Good (k : ℕ) (φ : G.Dart → ZMod k) (ψ : G.Dart → ℤ) : Prop :=
  (∀ d, ψ d.symm = -ψ d) ∧ (∀ d, (ψ d : ZMod k) = φ d) ∧ ∀ d, |ψ d| < k

/-- The total excess. -/
noncomputable def pot (ψ : G.Dart → ℤ) : ℕ := ∑ v, (ex ψ v).natAbs

lemma exists_good {k : ℕ} (hk : 0 < k) (φ : G.Dart → ZMod k) (ha : ∀ d, φ d.symm = -φ d) :
    ∃ ψ, Good k φ ψ := by
  haveI : NeZero k := NeZero.of_pos hk
  let e := Fintype.equivFin V
  refine ⟨fun d => if e d.fst < e d.snd then ((φ d).val : ℤ) else -((φ d.symm).val : ℤ),
    fun d => ?_, fun d => ?_, fun d => ?_⟩
  · have hne : e d.fst ≠ e d.snd := fun h => d.adj.ne (e.injective h)
    simp only [Dart.symm_toProd, Prod.fst_swap, Prod.snd_swap, Dart.symm_symm]
    by_cases h : e d.fst < e d.snd
    · rw [if_pos h, if_neg (lt_asymm h)]
    · rw [if_neg h, if_pos (lt_of_le_of_ne (not_lt.mp h) (Ne.symm hne)), neg_neg]
  · dsimp only
    split_ifs
    · simp
    · push_cast
      rw [ZMod.natCast_zmod_val, ha, neg_neg]
  · have h1 := ZMod.val_lt (φ d)
    have h2 := ZMod.val_lt (φ d.symm)
    dsimp only
    split_ifs
    · rw [abs_of_nonneg (by positivity)]
      exact_mod_cast h1
    · rw [abs_neg, abs_of_nonneg (by positivity)]
      exact_mod_cast h2

lemma dvd_ex {k : ℕ} {φ : G.Dart → ZMod k} {ψ : G.Dart → ℤ} (hψ : Good k φ ψ)
    (hc : ∀ v, ∑ d ∈ univ.filter (fun d : G.Dart ↦ d.fst = v), φ d = 0) (v : V) :
    (k : ℤ) ∣ ex ψ v := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ex, Int.cast_sum]
  simp only [hψ.2.1]
  exact hc v

/-- **Augmenting along a positive path.** -/
lemma augment {k : ℕ} {φ : G.Dart → ZMod k} {ψ : G.Dart → ℤ} (hψ : Good k φ ψ)
    (hdvd : ∀ v, (k : ℤ) ∣ ex ψ v) {s t : V} (p : G.Walk s t) (hp : p.IsPath)
    (hpos : ∀ d ∈ p.darts, 0 < ψ d) (hs : 0 < ex ψ s) (ht : ex ψ t < 0) :
    ∃ ψ', Good k φ ψ' ∧ pot ψ' < pot ψ := by
  obtain ⟨ha, hcast, hbd⟩ := hψ
  have hnd : p.darts.Nodup := Walk.darts_nodup_of_support_nodup hp.support_nodup
  have hc1 : ∀ d, p.darts.count d ≤ 1 := List.nodup_iff_count_le_one.mp hnd
  have hst : s ≠ t := by rintro rfl; omega
  set ψ' : G.Dart → ℤ := fun d => ψ d - k * (p.darts.count d : ℤ) + k * (p.darts.count d.symm : ℤ)
    with hψ'
  have hex : ∀ v, ex ψ' v = ex ψ v - k * (if s = v then 1 else 0) + k * (if t = v then 1 else 0) := by
    intro v
    have h1 : ex ψ' v = ex ψ v - k * ∑ d ∈ univ.filter (fun d : G.Dart ↦ d.fst = v),
        (p.darts.count d : ℤ) + k * ∑ d ∈ univ.filter (fun d : G.Dart ↦ d.fst = v),
        (p.darts.count d.symm : ℤ) := by
      simp only [ex, hψ', sum_add_distrib, sum_sub_distrib, mul_sum]
    rw [h1, sum_filter_symm (fun d => (p.darts.count d : ℤ)), sum_count_filter, sum_count_filter]
    have := countP_darts_fst_add p v
    linear_combination -(k : ℤ) * this
  refine ⟨ψ', ⟨fun d => ?_, fun d => ?_, fun d => ?_⟩, ?_⟩
  · show ψ d.symm - k * (p.darts.count d.symm : ℤ) + k * (p.darts.count d.symm.symm : ℤ) =
      -(ψ d - k * (p.darts.count d : ℤ) + k * (p.darts.count d.symm : ℤ))
    rw [Dart.symm_symm, ha]
    ring
  · simp [hψ', hcast]
  · have hd1 := hc1 d
    have hd2 := hc1 d.symm
    have hb := hbd d
    rw [abs_lt] at hb ⊢
    simp only [hψ']
    interval_cases hcd : p.darts.count d <;> interval_cases hcs : p.darts.count d.symm
    · simp; omega
    · have := hpos d.symm (List.count_pos_iff.mp (by omega))
      rw [ha] at this
      simp; omega
    · have := hpos d (List.count_pos_iff.mp (by omega))
      simp; omega
    · have h1 := hpos d (List.count_pos_iff.mp (by omega))
      have h2 := hpos d.symm (List.count_pos_iff.mp (by omega))
      rw [ha] at h2
      omega
  · have hks : (k : ℤ) ≤ ex ψ s := by
      obtain ⟨c, hc⟩ := hdvd s
      rw [hc] at hs ⊢
      have : 0 < c := pos_of_mul_pos_right hs (by positivity)
      nlinarith
    have hkt : ex ψ t ≤ -(k : ℤ) := by
      obtain ⟨c, hc⟩ := hdvd t
      rw [hc] at ht ⊢
      have : c < 0 := neg_of_mul_neg_right ht (by positivity)
      nlinarith
    have hk : (0 : ℤ) < k := by
      rcases (Nat.cast_nonneg k : (0 : ℤ) ≤ k).lt_or_eq with h | h
      · exact h
      · have := hdvd s
        rw [← h, zero_dvd_iff] at this
        omega
    apply sum_lt_sum
    · intro v _
      rw [hex v]
      zify
      by_cases hsv : s = v
      · subst hsv
        rw [if_pos rfl, if_neg (Ne.symm hst)]
        rw [abs_of_nonneg (by omega), abs_of_pos (by omega)]
        omega
      · by_cases htv : t = v
        · subst htv
          rw [if_neg hsv, if_pos rfl]
          rw [abs_of_nonpos (by omega), abs_of_neg (by omega)]
          omega
        · rw [if_neg hsv, if_neg htv]
          simp
    · refine ⟨s, mem_univ _, ?_⟩
      rw [hex s, if_pos rfl, if_neg (Ne.symm hst)]
      zify
      rw [abs_of_nonneg (by omega), abs_of_pos (by omega)]
      omega

/-- **Tutte.** A nowhere-zero `ℤ/k`-flow lifts to a nowhere-zero integer flow with values in
`(−k, k)`. -/
theorem lift {k : ℕ} (hk : 0 < k) (φ : G.Dart → ZMod k) (ha : ∀ d, φ d.symm = -φ d)
    (hn : ∀ d, φ d ≠ 0) (hc : ∀ v, ∑ d ∈ univ.filter (fun d : G.Dart ↦ d.fst = v), φ d = 0) :
    ∃ ψ : G.Dart → ℤ, (∀ d, ψ d.symm = -ψ d) ∧ (∀ d, ψ d ≠ 0 ∧ |ψ d| < k) ∧
      ∀ v, ∑ d ∈ univ.filter (fun d : G.Dart ↦ d.fst = v), ψ d = 0 := by
  have hex : ∃ n, ∃ ψ, Good k φ ψ ∧ pot ψ = n := by
    obtain ⟨ψ, hψ⟩ := exists_good hk φ ha
    exact ⟨_, ψ, hψ, rfl⟩
  obtain ⟨ψ, hψ, hpot⟩ := Nat.find_spec hex
  have hmin : ∀ ψ', Good k φ ψ' → ¬ pot ψ' < pot ψ := by
    intro ψ' hψ' hlt
    rw [hpot] at hlt
    exact Nat.find_min hex hlt ⟨ψ', hψ', rfl⟩
  have hzero : ∀ v, ex ψ v = 0 := by
    by_contra hne
    push_neg at hne
    obtain ⟨s, hs⟩ : ∃ s, 0 < ex ψ s := by
      by_contra hall
      push_neg at hall
      obtain ⟨v, hv⟩ := hne
      have h1 := sum_ex ψ hψ.1
      have h2 : ∑ w, ex ψ w < 0 :=
        sum_neg' (fun w _ => hall w) ⟨v, mem_univ _, lt_of_le_of_ne (hall v) hv⟩
      omega
    set R : Finset V := univ.filter fun v => ∃ p : G.Walk s v, ∀ d ∈ p.darts, 0 < ψ d with hR
    by_cases hneg : ∃ t ∈ R, ex ψ t < 0
    · obtain ⟨t, htR, ht⟩ := hneg
      obtain ⟨p, hp⟩ := (mem_filter.mp htR).2
      obtain ⟨ψ', hψ', hlt⟩ := augment hψ (dvd_ex hψ hc) p.bypass p.bypass_isPath
        (fun d hd => hp d (Walk.darts_bypass_subset_darts p hd)) hs ht
      exact hmin ψ' hψ' hlt
    · push_neg at hneg
      have hsR : s ∈ R := mem_filter.mpr ⟨mem_univ _, Walk.nil, by simp⟩
      have h1 : 0 < ∑ v ∈ R, ex ψ v := by
        rw [← add_sum_erase R _ hsR]
        have : 0 ≤ ∑ v ∈ R.erase s, ex ψ v := sum_nonneg fun v hv => hneg v (mem_of_mem_erase hv)
        omega
      have h2 : ∑ v ∈ R, ex ψ v ≤ 0 := by
        rw [sum_ex_set ψ hψ.1 R]
        refine sum_nonpos fun d hd => ?_
        obtain ⟨hfR, hsnR⟩ := (mem_filter.mp hd).2
        by_contra hpos
        push_neg at hpos
        apply hsnR
        obtain ⟨p, hp⟩ := (mem_filter.mp hfR).2
        refine mem_filter.mpr ⟨mem_univ _, p.concat d.adj, fun d' hd' => ?_⟩
        rw [Walk.darts_concat, List.concat_eq_append, List.mem_append] at hd'
        rcases hd' with hd' | hd'
        · exact hp d' hd'
        · rw [List.mem_singleton] at hd'
          rw [hd']
          exact hpos
      omega
  refine ⟨ψ, hψ.1, fun d => ⟨fun h0 => hn d ?_, hψ.2.2 d⟩, hzero⟩
  rw [← hψ.2.1 d, h0, Int.cast_zero]

end Tutte

end SixFlow
