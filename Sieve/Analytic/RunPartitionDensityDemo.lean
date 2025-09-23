/-
  Sieve/Analytic/RunPartitionDensityDemo.lean

  Demo: given P : PartitionBetaLower, if (∑ β r) · |H| ≥ 1 then there exists
  a heavy point whose window hits (Stage-3 façade).
-/
import Mathlib
import Sieve.Analytic.ResidueToDensityFromPartition
import Sieve.Analytic.HitFromDensity

noncomputable section
open Classical

namespace Sieve
namespace Analytic

/-- Parametric demo: partition data ⇒ density ⇒ heavy hit when (∑ β)·|H| ≥ 1. -/
theorem partition_density_demo_exists
    (P : PartitionBetaLower)
    (W : Sieve.MaynardWeights.Weight) (τ : ℝ)
    (H : Finset ℤ) (HS : Sieve.Stage3.HitSystem)
    (hne : (Sieve.MTCore.heavySet W τ).Nonempty)
    (hδ : 1 ≤ (∑ r ∈ Finset.range P.q, P.β r) * (H.card : ℝ)) :
    ∃ n ∈ Sieve.MTCore.heavySet W τ, ∃ k ∈ H, HS.isHit (n + k) := by
  classical
  -- Package partition → density
  let D := WindowDensityLower_ofPartition P
  -- D.δ = ∑ β; use the average ≥ 1 ⇒ hit bridge
  simpa using
    exists_heavy_hit_from_density
      (D := D) (W := W) (τ := τ) (H := H) (HS := HS) (hne := hne) (hδ := hδ)

/-- Smoke: symbolically touch to catch signature drift. -/
theorem partition_density_demo_wired : True := by
  let _ := @partition_density_demo_exists
  exact True.intro

end Analytic
end Sieve
