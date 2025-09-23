/-
  Sieve/Analytic/RunBVFirstFromFirstMomentDemo.lean

  Demo: If you provide a first-moment lower bound
        (|heavy| : ℝ) * c ≤ ∑_{n∈heavy} windowSum H hitIndicator n
  with c ≥ 1, then the Stage-3 average is ≥ 1 and we get a heavy hit.
-/
import Mathlib
import Sieve.Analytic.BVFirstFromFirstMoment
import Sieve.Analytic.AvgFromFirstMoment
import Sieve.Stage3PrimeFacade

noncomputable section
open Classical

namespace Sieve
namespace Analytic

/-- Demo theorem: first-moment bound with `c ≥ 1` implies existence of a heavy hit. -/
theorem firstMoment_demo_exists
    (P : BVParams) (_TB : BVToolboxProgressionsSig)
    (F : FirstMomentPieces P)
    (W : Sieve.MaynardWeights.Weight) (τ : ℝ)
    (H : Finset ℤ) (HS : Sieve.Stage3.HitSystem)
    (hne : (Sieve.MTCore.heavySet W τ).Nonempty)
    (hc : 1 ≤ F.c) :
    ∃ n ∈ Sieve.MTCore.heavySet W τ, ∃ k ∈ H, HS.isHit (n + k) := by
  classical
  -- From first-moment pieces: c ≤ average over the heavy set
  have h_avg_ge_c :
      F.c ≤ Sieve.Stage3.avgOver (Sieve.MTCore.heavySet W τ)
                (Sieve.Stage3.windowSum H (Sieve.Stage3.hitIndicator HS)) := by
    exact
      avgOver_heavy_ge_of_sum_ge
        (W := W) (τ := τ) (H := H) (HS := HS) (hne := hne)
        (c := F.c)
        (h := F.sum_ge W τ H HS hne)
  -- Hence average ≥ 1
  have hAvg :
      1 ≤ Sieve.Stage3.avgOver (Sieve.MTCore.heavySet W τ)
            (Sieve.Stage3.windowSum H (Sieve.Stage3.hitIndicator HS)) :=
    le_trans hc h_avg_ge_c
  -- Stage-3 extraction from average ≥ 1
  exact
    Sieve.Stage3.exists_heavy_with_hit_from_avg_ge_one
      (W := W) (τ := τ) (H := H) (HS := HS) (hne := hne) (hAvg := hAvg)

/-- Sanity: the demo compiles and can be referenced. -/
theorem firstMoment_demo_wired
    (P : BVParams) (_TB : BVToolboxProgressionsSig) (_F : FirstMomentPieces P) : True := True.intro

end Analytic
end Sieve
