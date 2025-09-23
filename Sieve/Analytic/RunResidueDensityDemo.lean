/-
  Sieve/Analytic/RunResidueDensityDemo.lean

  Demo: from residue-based data `I : ResidueToDensityInput`,
  if δ · |H| ≥ 1 then there exists a heavy point whose window hits.
-/
import Mathlib
import Sieve.Analytic.ResidueToDensityTemplate
import Sieve.Analytic.HitFromDensity

noncomputable section
open Classical

namespace Sieve
namespace Analytic

/-- Parametric demo: residue data ⇒ density ⇒ heavy hit when δ·|H| ≥ 1. -/
theorem residue_density_demo_exists
    (I : ResidueToDensityInput)
    (W : Sieve.MaynardWeights.Weight) (τ : ℝ)
    (H : Finset ℤ) (HS : Sieve.Stage3.HitSystem)
    (hne : (Sieve.MTCore.heavySet W τ).Nonempty)
    (hδ : 1 ≤ I.δ * (H.card : ℝ)) :
    ∃ n ∈ Sieve.MTCore.heavySet W τ, ∃ k ∈ H, HS.isHit (n + k) := by
  classical
  -- Package residues → density
  let D := WindowDensityLower_ofResidues I
  -- Density ⇒ first-moment ⇒ average ≥ 1 ⇒ heavy hit
  exact exists_heavy_hit_from_density
    (D := D) (W := W) (τ := τ) (H := H) (HS := HS) (hne := hne) (hδ := hδ)

/-- Smoke: symbolically touch to catch signature drift. -/
theorem residue_density_demo_wired : True := by
  let _ := @residue_density_demo_exists
  exact True.intro

end Analytic
end Sieve
