import Mathlib
import Sieve.AdmissibleTwin
import Sieve.ConfigBuilders
import Sieve.ConstWeight

/-
  Sieve/EndToEnd.lean
  Small API: build ready-to-use Stage-2 "reports" for twins + constant weights.

  NOTE: We intentionally keep this decoupled from any separate Stage-2 Report module.
  We define a minimal `Report` here with just the `.B` field used by downstream demos.
-/

noncomputable section
open Classical
open Finset
open scoped BigOperators

namespace Sieve.EndToEnd

/-- Symmetric integer window `[-M, M]` (cast-friendly). -/
def window (M : ℕ) : Finset ℤ :=
  Finset.Icc (-(M : ℤ)) (M : ℤ)

/-- Minimal record we need from a Stage-2 "report": currently only the quadratic mass `B`. -/
structure Report where
  B : ℝ

/-- End-to-end Stage-2 report for **twins + constant weight** with the conservative contract. -/
def report_twin_const_conservative (_M : ℕ) (_c : ℝ) (_hc : 0 ≤ _c) : Report := by
  -- In the conservative contract, the quadratic mass term is 0.
  exact ⟨0⟩

/-- End-to-end Stage-2 report for **twins + constant weight** with the simple (non-zero) contract. -/
def report_twin_const_simple (M : ℕ) (Mabs : ℝ) (_c : ℝ) (_hc : 0 ≤ _c) : Report := by
  -- In the simple contract, B = (|[-M,M]|)^2 * Mabs^2.
  let supp : Finset ℤ := window M
  exact ⟨((supp.card : ℝ)^2) * Mabs^2⟩

/-- Sanity: `B = 0` in the conservative case. -/
example (M : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    (report_twin_const_conservative M c hc).B = 0 := rfl

/-- Sanity: `B = (card [-M,M])^2 · Mabs^2` in the simple case. -/
example (M : ℕ) (Mabs c : ℝ) (hc : 0 ≤ c) :
    (report_twin_const_simple M Mabs c hc).B = ((window M).card : ℝ)^2 * Mabs^2 := rfl

end Sieve.EndToEnd
