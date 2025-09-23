/-
  Sieve/Analytic/RunResidueSumToyDemo.lean

  Demo: Use the toy residue-sum density (δ = 0). If we *assume* δ·|H| ≥ 1,
  the Stage-3 bridge yields a heavy point with a hit. This keeps the full
  path exercised while we work on a nontrivial γ later.
-/
import Mathlib
import Sieve.Analytic.ResidueSumToy
import Sieve.Analytic.HitFromDensity

noncomputable section
open Classical

namespace Sieve
namespace Analytic

/-- Demo: from the toy density `ToyResidueSumDensity`, if δ·|H| ≥ 1 then ∃ heavy hit. -/
theorem toy_residue_sum_demo_exists
    (W : Sieve.MaynardWeights.Weight) (τ : ℝ)
    (H : Finset ℤ) (HS : Sieve.Stage3.HitSystem)
    (hne : (Sieve.MTCore.heavySet W τ).Nonempty)
    (hδ : 1 ≤ ToyResidueSumDensity.δ * (H.card : ℝ)) :
    ∃ n ∈ Sieve.MTCore.heavySet W τ, ∃ k ∈ H, HS.isHit (n + k) := by
  -- Stage-3 bridge from density to a hit:
  simpa using
    exists_heavy_hit_from_density
      (D := ToyResidueSumDensity)
      (W := W) (τ := τ) (H := H) (HS := HS) (hne := hne) (hδ := hδ)

/-- Smoke: symbolically touch to catch signature drift. -/
theorem toy_residue_sum_demo_wired : True := by
  let _ := @toy_residue_sum_demo_exists
  exact True.intro

end Analytic
end Sieve
