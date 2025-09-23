/-
  Sieve/Analytic/RunResiduePartitionSumDemo.lean

  Demo: If you provide residue-sum data with constant γ and `(γ · |H|) ≥ 1`,
  then there exists a heavy point whose window contains a hit.
-/
import Mathlib
import Sieve.Analytic.ResidueToPartitionSumConcrete
import Sieve.Analytic.HitFromDensity

noncomputable section
open Classical

namespace Sieve
namespace Analytic

/-- Demo: residue-sum ⇒ density (δ=γ) ⇒ heavy hit when γ·|H| ≥ 1. -/
theorem residue_partition_sum_demo_exists
    (C : ResidueToPartitionSumConcrete)
    (W : Sieve.MaynardWeights.Weight) (τ : ℝ)
    (H : Finset ℤ) (HS : Sieve.Stage3.HitSystem)
    (hne : (Sieve.MTCore.heavySet W τ).Nonempty)
    (hγ : 1 ≤ C.γ * (H.card : ℝ)) :
    ∃ n ∈ Sieve.MTCore.heavySet W τ, ∃ k ∈ H, HS.isHit (n + k) := by
  classical
  let D := WindowDensityLower_ofPartitionSumConcrete C
  -- Bridge from density to hit.
  simpa using
    exists_heavy_hit_from_density
      (D := D) (W := W) (τ := τ) (H := H) (HS := HS) (hne := hne) (hδ := hγ)

/-- Smoke: symbolically touch to catch shape drift. -/
theorem residue_partition_sum_demo_wired : True := by
  let _ := @residue_partition_sum_demo_exists
  exact True.intro

end Analytic
end Sieve
