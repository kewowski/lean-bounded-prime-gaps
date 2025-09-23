/-
  Sieve/Analytic/BVMainIneq.lean
  UTF-8 (no BOM), ASCII-only.

  Purpose
  -------
  A tiny *spec shim* capturing exactly the single analytic inequality
  Stage-3 needs from BV/EH, and packaging it into `AvgWindowHitLB`.

  Linter-friendly: use `_hne` to avoid "unused variable" warnings.
-/
import Mathlib
import Sieve.Analytic.Constants
import Sieve.AnalyticInputs
import Sieve.Analytic.BVMainRealize
import Sieve.Analytic.BVMainAssumptions

noncomputable section

namespace Sieve
namespace Analytic

/--
`BVMainIneq P` is the single analytic statement BV/EH must provide:

For every weights `W`, parameter `τ`, window `H`, hit system `HS`, and nonempty
heavy set, the BV lower formula is ≤ the heavy-set average of window hits.
-/
def BVMainIneq (P : BVParams) : Prop :=
  ∀ (W : Sieve.MaynardWeights.Weight) (τ : ℝ)
    (H : Finset ℤ) (HS : Sieve.Stage3.HitSystem)
    (_hne : (Sieve.MTCore.heavySet W τ).Nonempty),
    P.lowerFormula
      ≤ Sieve.Stage3.avgOver (Sieve.MTCore.heavySet W τ)
          (Sieve.Stage3.windowSum H (Sieve.Stage3.hitIndicator HS))

/-- From a proof of `BVMainIneq P`, build the Stage-3 analytic input. -/
def AI_of_BV_ofIneq (P : BVParams) (h : BVMainIneq P) : AvgWindowHitLB :=
  AI_of_BV_fromLowerBound P (by
    intro W τ H HS hne
    exact h W τ H HS hne)

/-- Variant carrying `BVMainAssumptions P` alongside (not used here, but ergonomic). -/
def AI_of_BV_ofIneq' (P : BVParams) (_A : BVMainAssumptions P) (h : BVMainIneq P) :
    AvgWindowHitLB :=
  AI_of_BV_ofIneq P h

end Analytic
end Sieve
