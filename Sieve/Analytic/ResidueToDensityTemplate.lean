/-
  Sieve/Analytic/ResidueToDensityTemplate.lean

  Purpose
  -------
  A *template* that turns a residue-class argument (pigeonhole + partition + DPS, etc.)
  into a pointwise window-density lower bound, packaged as `WindowDensityLower`.

  How to use
  ----------
  • Fill in `ResidueToDensityInput.pointwise_from_residues` with your canonical
    residue proof (using the helpers you already have:
      - `ResiduePartition`   (sum over residues),
      - `ResiduePointwise`   (evaluate a fixed residue’s contribution),
      - `ResiduePigeonhole`  (choose a good residue),
      - `DPSAliases` / `OrthogonalityConvenience` as needed).
  • Then call `WindowDensityLower_ofResidues I` to obtain a `WindowDensityLower`,
    which plugs straight into:
      - `FirstMomentVar_ofDensity`,
      - `exists_heavy_hit_from_density` (average ≥ 1 ⇒ heavy hit).

  Notes
  -----
  • This module is intentionally light: no analysis, no axioms, no sorry.
  • All binders are fully explicit and shaped in Stage-3’s `(W, τ, H, HS, hne, n, hn)` style.
-/

import Mathlib
import Sieve.Stage3
import Sieve.Stage3Window
import Sieve.Analytic.FirstMomentFromToyDensity  -- for WindowDensityLower

noncomputable section
open Classical

namespace Sieve
namespace Analytic

/-- Inputs you provide from a residue-class argument in canonical shapes.
    `δ` is the density you can guarantee pointwise over the heavy set. -/
structure ResidueToDensityInput where
  δ : ℝ
  /-- Your *residue-based* pointwise lower bound:
      for each heavy `n`, the window sum is ≥ `δ · |H|`.
      Fill this using your residue lemmas (partition/pointwise/pigeonhole/DPS). -/
  pointwise_from_residues :
    ∀ (W : Sieve.MaynardWeights.Weight) (τ : ℝ)
      (H : Finset ℤ) (HS : Sieve.Stage3.HitSystem)
      (_hne : (Sieve.MTCore.heavySet W τ).Nonempty)
      (n : ℤ) (_hn : n ∈ Sieve.MTCore.heavySet W τ),
      δ * (H.card : ℝ)
        ≤ Sieve.Stage3.windowSum H (Sieve.Stage3.hitIndicator HS) n

/-- Package residue data into a ready `WindowDensityLower`. -/
def WindowDensityLower_ofResidues (I : ResidueToDensityInput) : WindowDensityLower :=
{ δ := I.δ
, pointwise := by
    intro W τ H HS hne n hn
    exact I.pointwise_from_residues W τ H HS hne n hn
}

/-- Smoke: symbolically touch the constructor so signature drift is caught. -/
theorem residue_to_density_template_wired : True := by
  let _ := @WindowDensityLower_ofResidues
  exact True.intro

end Analytic
end Sieve
