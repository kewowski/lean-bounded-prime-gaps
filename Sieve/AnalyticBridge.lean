/-
  Sieve/AnalyticBridge.lean
  A minimal contract for analytic lower bounds on average window-hit counts,
  and bridge lemmas into the Stage-3 façade (existence of hits).
-/
import Mathlib
import Sieve.MTCore
import Sieve.Stage3Window
import Sieve.Stage3PrimeFacade
import Sieve.Stage3PrimeCounts
import Sieve.Stage3PrimeCountsNat

set_option linter.unusedVariables false

noncomputable section
open Classical BigOperators

namespace Sieve
namespace Analytic

/-- Contract: an average lower bound on window *hit counts* over the τ-heavy set. -/
structure AvgWindowHitLB where
  /-- A real-valued lower bound depending on `(W, τ, H, HS)` and a proof that the heavy set is nonempty. -/
  lower :
    ∀ (W : Sieve.MaynardWeights.Weight) (τ : ℝ)
      (H : Finset ℤ) (HS : Sieve.Stage3.HitSystem),
      (Sieve.MTCore.heavySet W τ).Nonempty → ℝ
  /-- The lower bound is indeed ≤ the heavy-set average of the window hit count. -/
  le_avg :
    ∀ (W : Sieve.MaynardWeights.Weight) (τ : ℝ)
      (H : Finset ℤ) (HS : Sieve.Stage3.HitSystem)
      (hne : (Sieve.MTCore.heavySet W τ).Nonempty),
      lower W τ H HS hne
        ≤ Sieve.Stage3.avgOver (Sieve.MTCore.heavySet W τ)
            (Sieve.Stage3.windowSum H (Sieve.Stage3.hitIndicator HS))

/-- **Bridge (existence, `t = 1`)**:
If the analytic lower bound at `(W,τ,H,HS)` is ≥ 1, then there is a heavy point whose window contains a hit. -/
theorem exists_heavy_hit_of_lb_ge_one
    (AI : AvgWindowHitLB)
    (W : Sieve.MaynardWeights.Weight) (τ : ℝ)
    (H : Finset ℤ) (HS : Sieve.Stage3.HitSystem)
    (hne : (Sieve.MTCore.heavySet W τ).Nonempty)
    (h1 : 1 ≤ AI.lower W τ H HS hne) :
    ∃ n ∈ Sieve.MTCore.heavySet W τ, ∃ h ∈ H, HS.isHit (n + h) := by
  classical
  have hAvg :
      1 ≤ Sieve.Stage3.avgOver (Sieve.MTCore.heavySet W τ)
              (Sieve.Stage3.windowSum H (Sieve.Stage3.hitIndicator HS)) :=
    le_trans h1 (AI.le_avg W τ H HS hne)
  exact
    Sieve.Stage3.exists_heavy_with_hit_from_avg_ge_one
      (W := W) (τ := τ) (H := H) (HS := HS) hne hAvg

/-- **Bridge (integer threshold)**:
If the analytic lower bound is ≥ `k : ℕ`, then there is a heavy point whose window
has at least `k` hits (cardinality statement). -/
theorem exists_heavy_with_atLeast_k_hits_of_lb_ge_k
    (AI : AvgWindowHitLB)
    (W : Sieve.MaynardWeights.Weight) (τ : ℝ)
    (H : Finset ℤ) (HS : Sieve.Stage3.HitSystem)
    (hne : (Sieve.MTCore.heavySet W τ).Nonempty)
    (k : ℕ)
    (hk : (k : ℝ) ≤ AI.lower W τ H HS hne) :
    ∃ n ∈ Sieve.MTCore.heavySet W τ,
      k ≤ (H.filter (fun h => HS.isHit (n + h))).card := by
  classical
  have hAvg :
      (k : ℝ) ≤ Sieve.Stage3.avgOver (Sieve.MTCore.heavySet W τ)
                (Sieve.Stage3.windowSum H (Sieve.Stage3.hitIndicator HS)) :=
    le_trans hk (AI.le_avg W τ H HS hne)
  exact
    Sieve.Stage3.exists_heavy_with_atLeast_k_hits
      (W := W) (τ := τ) (H := H) (HS := HS) hne k hAvg

end Analytic
end Sieve

