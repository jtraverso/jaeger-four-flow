/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import JaegerLib.Jaeger
public import SixFlowLib.SixFlowTutte
public import SixFlowLib.SixFlowConvert

/-!
# Seymour's 6-flow theorem and Tutte's group-to-integer flow theorem

For a finite simple graph `G`, a *nowhere-zero `A`-flow* (for an abelian group `A`) is an
antisymmetric function on the darts of `G` with no zero value that is conserved at every vertex
(`SixFlow.IsNowhereZeroGroupFlow`). Integer `k`-flows are `Jaeger.IsNowhereZeroFlow G k`.

* `SixFlow.integer_flow_of_zmod`: **Tutte's theorem (1949).** For `k > 0`, every nowhere-zero
  `ℤ/k`-flow `φ` lifts to a nowhere-zero integer `k`-flow `ψ` (values in `(−k, k) \ {0}`) with
  `ψ ≡ φ (mod k)`.
* `SixFlow.zmod_flow_of_integer`: conversely, the reduction modulo `k` of a nowhere-zero integer
  `k`-flow is a nowhere-zero `ℤ/k`-flow.
* `SixFlow.seymour_six_flow`: **Seymour's 6-flow theorem (1981).** Every finite bridgeless graph
  has a nowhere-zero integer 6-flow.
-/

@[expose] public section

open Finset SimpleGraph

namespace SixFlow

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `φ` is a nowhere-zero `A`-flow on `G`: antisymmetric on darts, nonzero on every dart, and
conserved at every vertex. -/
def IsNowhereZeroGroupFlow {A : Type*} [AddCommGroup A] (G : SimpleGraph V) [DecidableRel G.Adj]
    (φ : G.Dart → A) : Prop :=
  (∀ d, φ d.symm = -φ d) ∧ (∀ d, φ d ≠ 0) ∧
    ∀ v, ∑ d ∈ univ.filter (fun d : G.Dart ↦ d.fst = v), φ d = 0

/-- **Tutte (1949).** Every nowhere-zero `ℤ/k`-flow `φ` lifts to a nowhere-zero integer `k`-flow
`ψ` with `ψ ≡ φ (mod k)` on every dart. -/
theorem integer_flow_of_zmod (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (hk : 0 < k)
    (φ : G.Dart → ZMod k) (hφ : IsNowhereZeroGroupFlow G φ) :
    ∃ ψ : G.Dart → ℤ, Jaeger.IsNowhereZeroFlow G k ψ ∧ ∀ d, (ψ d : ZMod k) = φ d := by
  obtain ⟨ha, hn, hc⟩ := hφ
  exact Tutte.lift hk φ ha hn hc

/-- The reduction modulo `k` of a nowhere-zero integer `k`-flow is a nowhere-zero `ℤ/k`-flow. -/
theorem zmod_flow_of_integer (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ}
    (ψ : G.Dart → ℤ) (hψ : Jaeger.IsNowhereZeroFlow G k ψ) :
    IsNowhereZeroGroupFlow G (fun d => (ψ d : ZMod k)) := by
  obtain ⟨ha, hn, hc⟩ := hψ
  refine ⟨fun d => by simp [ha], fun d => ?_, fun v => ?_⟩
  · intro h0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h0
    exact (hn d).1 (Int.eq_zero_of_abs_lt_dvd h0 (hn d).2)
  · simp only
    rw [← Int.cast_sum, hc v, Int.cast_zero]

/-- **Seymour's 6-flow theorem (1981).** Every finite bridgeless graph has a nowhere-zero integer
6-flow. -/
theorem seymour_six_flow (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : ∀ e ∈ G.edgeSet, ¬ G.IsBridge e) :
    ∃ φ : G.Dart → ℤ, Jaeger.IsNowhereZeroFlow G 6 φ := by
  obtain ⟨φ, ha, hn, hc⟩ := Convert.exists_zmod6_flow hG
  obtain ⟨ψ, hψ, -⟩ := integer_flow_of_zmod G (k := 2 * 3) (by norm_num) φ ⟨ha, hn, hc⟩
  exact ⟨ψ, hψ⟩

end SixFlow
