/-
  Sieve/Analytic/AvgNonneg.lean

  Nonnegativity helpers for Stage-3 averages and window sums.
  These are leaf-level lemmas used to guarantee a trivial (but real) lower bound.
-/
import Mathlib
import Sieve.Stage3Window
import Sieve.Stage3PrimeFacade
import Sieve.MTCore

noncomputable section
open Classical

namespace Sieve
namespace Analytic

/-- If `g ≥ 0` on a finite set `A`, then the average of `g` over `A` is ≥ 0. -/
lemma avgOver_nonneg_of_nonneg
    (A : Finset ℤ) (g : ℤ → ℝ)
    (hnonneg : ∀ n ∈ A, 0 ≤ g n) :
    0 ≤ Sieve.Stage3.avgOver A g := by
  classical
  have hsum : 0 ≤ (∑ n ∈ A, g n) := by
    apply Finset.sum_nonneg
    intro n hn
    exact hnonneg n hn
  have hden : 0 ≤ (A.card : ℝ) := by exact_mod_cast (Nat.zero_le A.card)
  simpa [Sieve.Stage3.avgOver] using div_nonneg hsum hden

/-- Each window hit-indicator sum is ≥ 0 (sum of 0/1s). -/
lemma window_hitIndicator_nonneg
    (H : Finset ℤ) (HS : Sieve.Stage3.HitSystem) (n : ℤ) :
    0 ≤ Sieve.Stage3.windowSum H (Sieve.Stage3.hitIndicator HS) n := by
  classical
  unfold Sieve.Stage3.windowSum Sieve.Stage3.hitIndicator
  apply Finset.sum_nonneg
  intro h hh
  by_cases ph : HS.isHit (n + h)
  · simp [ph]
  · simp [ph]

/-- Heavy-set average of window-hit counts is nonnegative. -/
lemma avgOver_heavy_window_nonneg
    (W : Sieve.MaynardWeights.Weight) (τ : ℝ)
    (H : Finset ℤ) (HS : Sieve.Stage3.HitSystem) :
    0 ≤ Sieve.Stage3.avgOver (Sieve.MTCore.heavySet W τ)
          (Sieve.Stage3.windowSum H (Sieve.Stage3.hitIndicator HS)) := by
  classical
  refine avgOver_nonneg_of_nonneg
    (A := Sieve.MTCore.heavySet W τ)
    (g := fun n => Sieve.Stage3.windowSum H (Sieve.Stage3.hitIndicator HS) n)
    ?_
  intro n hn
  exact window_hitIndicator_nonneg H HS n

/-- Tiny compile-touch so CI keeps this surface hot. -/
theorem avg_nonneg_compiles : True := by
  exact True.intro

end Analytic
end Sieve
