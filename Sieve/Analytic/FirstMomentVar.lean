/-
  Sieve/Analytic/FirstMomentVar.lean

  Variable (instance-dependent) first-moment bridge:
  If for each (W, τ, H, HS, hne) we have
    (|heavy| : ℝ) * c(W,τ,H,HS,hne) ≤ ∑_{n∈heavy} windowSum H hitIndicator n,
  then we obtain an AvgWindowHitLB with lower = c(…).
-/
import Mathlib
import Sieve.Stage3
import Sieve.Stage3Window
import Sieve.Analytic.AvgFromFirstMoment
import Sieve.Analytic.AIConstructors  -- AnalyticInputs.ofLower

noncomputable section
open Classical

namespace Sieve
namespace Analytic

/-- Per-instance first-moment package. -/
structure FirstMomentVar where
  c :
    ∀ (W : Sieve.MaynardWeights.Weight) (τ : ℝ)
      (_H : Finset ℤ) (_HS : Sieve.Stage3.HitSystem)
      (_hne : (Sieve.MTCore.heavySet W τ).Nonempty), ℝ
  sum_ge :
    ∀ (W : Sieve.MaynardWeights.Weight) (τ : ℝ)
      (H : Finset ℤ) (HS : Sieve.Stage3.HitSystem)
      (hne : (Sieve.MTCore.heavySet W τ).Nonempty),
      ((Sieve.MTCore.heavySet W τ).card : ℝ) * c W τ H HS hne
        ≤ ∑ n ∈ Sieve.MTCore.heavySet W τ,
            Sieve.Stage3.windowSum H (Sieve.Stage3.hitIndicator HS) n

/-- Build `AvgWindowHitLB` with instance-dependent lower bound. -/
def AI_fromFirstMomentVar (F : FirstMomentVar) : AvgWindowHitLB :=
  AnalyticInputs.ofLower
    (fun W τ H HS hne => F.c W τ H HS hne)
    (fun W τ H HS hne =>
      -- average ≥ c by avg-from-first-moment
      avgOver_heavy_ge_of_sum_ge (W := W) (τ := τ) (H := H) (HS := HS)
        (hne := hne) (c := F.c W τ H HS hne)
        (h := F.sum_ge W τ H HS hne))

/-- Tiny smoke. -/
theorem firstMomentVar_wired (F : FirstMomentVar) : True := by
  let _ := AI_fromFirstMomentVar F
  exact True.intro

end Analytic
end Sieve
