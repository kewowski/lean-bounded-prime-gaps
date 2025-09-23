/-
  Sieve/Analytic/HitFromDensity.lean

  One-step wrapper: from a window-density lower bound δ and the size |H|,
  conclude there exists a heavy point whose window hits whenever δ·|H| ≥ 1.
-/
import Mathlib
import Sieve.Analytic.FirstMomentFromToyDensity
import Sieve.Analytic.AvgFromFirstMoment
import Sieve.Stage3PrimeFacade

noncomputable section
open Classical

namespace Sieve
namespace Analytic

/-- If every heavy point sees at least a δ-fraction of hits in its window,
    and δ·|H| ≥ 1, then some heavy window contains a hit. -/
theorem exists_heavy_hit_from_density
    (D : WindowDensityLower)
    (W : Sieve.MaynardWeights.Weight) (τ : ℝ)
    (H : Finset ℤ) (HS : Sieve.Stage3.HitSystem)
    (hne : (Sieve.MTCore.heavySet W τ).Nonempty)
    (hδ : 1 ≤ D.δ * (H.card : ℝ)) :
    ∃ n ∈ Sieve.MTCore.heavySet W τ, ∃ k ∈ H, HS.isHit (n + k) := by
  classical
  -- Package the density assumption as a variable first-moment input
  let F := FirstMomentVar_ofDensity D
  -- From the first-moment packaging we have avg ≥ δ·|H|
  have h_avg_ge_c :
      F.c W τ H HS hne ≤
        Sieve.Stage3.avgOver (Sieve.MTCore.heavySet W τ)
          (Sieve.Stage3.windowSum H (Sieve.Stage3.hitIndicator HS)) :=
    avgOver_heavy_ge_of_sum_ge
      (W := W) (τ := τ) (H := H) (HS := HS) (hne := hne)
      (c := F.c W τ H HS hne) (h := F.sum_ge W τ H HS hne)
  -- Unfold c = δ·|H| and get average ≥ 1
  have hAvg :
      1 ≤ Sieve.Stage3.avgOver (Sieve.MTCore.heavySet W τ)
            (Sieve.Stage3.windowSum H (Sieve.Stage3.hitIndicator HS)) := by
    simpa using le_trans hδ h_avg_ge_c
  -- Stage-3 extraction from average ≥ 1
  exact
    Sieve.Stage3.exists_heavy_with_hit_from_avg_ge_one
      (W := W) (τ := τ) (H := H) (HS := HS) (hne := hne) (hAvg := hAvg)

/-- Smoke: symbolically touch the theorem so signature drift is caught. -/
theorem hit_from_density_wired : True := by
  let _ := @exists_heavy_hit_from_density
  exact True.intro

end Analytic
end Sieve
