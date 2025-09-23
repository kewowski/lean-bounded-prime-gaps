/-
  Sieve/Analytic/RunBVFirstFromFirstMomentVarDemo.lean

  Demo: If c(W,τ,H,HS,hne) ≥ 1 and the first-moment inequality holds at that instance,
  then average ≥ 1 and Stage-3 yields a heavy hit.
-/
import Mathlib
import Sieve.Analytic.FirstMomentVar
import Sieve.Analytic.AvgFromFirstMoment
import Sieve.Stage3PrimeFacade

noncomputable section
open Classical

namespace Sieve
namespace Analytic

theorem firstMomentVar_demo_exists
    (F : FirstMomentVar)
    (W : Sieve.MaynardWeights.Weight) (τ : ℝ)
    (H : Finset ℤ) (HS : Sieve.Stage3.HitSystem)
    (hne : (Sieve.MTCore.heavySet W τ).Nonempty)
    (hc : 1 ≤ F.c W τ H HS hne) :
    ∃ n ∈ Sieve.MTCore.heavySet W τ, ∃ k ∈ H, HS.isHit (n + k) := by
  classical
  -- avg ≥ c
  have h_avg_ge_c :
      F.c W τ H HS hne ≤
        Sieve.Stage3.avgOver (Sieve.MTCore.heavySet W τ)
          (Sieve.Stage3.windowSum H (Sieve.Stage3.hitIndicator HS)) :=
    avgOver_heavy_ge_of_sum_ge
      (W := W) (τ := τ) (H := H) (HS := HS) (hne := hne)
      (c := F.c W τ H HS hne) (h := F.sum_ge W τ H HS hne)
  -- hence avg ≥ 1
  have hAvg :
      1 ≤ Sieve.Stage3.avgOver (Sieve.MTCore.heavySet W τ)
            (Sieve.Stage3.windowSum H (Sieve.Stage3.hitIndicator HS)) :=
    le_trans hc h_avg_ge_c
  -- Stage-3 extraction on average ≥ 1
  exact
    Sieve.Stage3.exists_heavy_with_hit_from_avg_ge_one
      (W := W) (τ := τ) (H := H) (HS := HS) (hne := hne) (hAvg := hAvg)

/-- smoke: compiles and references -/
theorem firstMomentVar_demo_wired (_F : FirstMomentVar) : True := True.intro

end Analytic
end Sieve
