/-
  Sieve/Analytic/AIConstructors.lean
  UTF-8 (no BOM), ASCII-only.

  Purpose
  -------
  Tiny helper constructors for the Stage-3 analytic interface `AvgWindowHitLB`.
  These are thin wrappers around `AnalyticInputs.mk`, letting us build an AI
  from any provided lower bound and a proof it is ≤ the Stage-3 average.

  Linter note:
  We use underscore-prefixed binder names (`_H`, `_HS`) in dependent function
  types to avoid "unused variable" warnings.
-/
import Mathlib
import Sieve.AnalyticInputs

noncomputable section

namespace Sieve
namespace AnalyticInputs

/--
Construct an `AvgWindowHitLB` from a candidate lower bound and a proof that it is
bounded above by the Stage-3 average window-hit count.
-/
@[inline] def ofLower
  (lower :
      ∀ (W : Sieve.MaynardWeights.Weight) (τ : ℝ)
        (_H : Finset ℤ) (_HS : Sieve.Stage3.HitSystem),
        (Sieve.MTCore.heavySet W τ).Nonempty → ℝ)
  (le_avg :
      ∀ (W : Sieve.MaynardWeights.Weight) (τ : ℝ)
        (_H : Finset ℤ) (_HS : Sieve.Stage3.HitSystem)
        (hne : (Sieve.MTCore.heavySet W τ).Nonempty),
        lower W τ _H _HS hne
          ≤ Sieve.Stage3.avgOver (Sieve.MTCore.heavySet W τ)
              (Sieve.Stage3.windowSum _H (Sieve.Stage3.hitIndicator _HS)))
  : AvgWindowHitLB :=
  AnalyticInputs.mk lower le_avg

end AnalyticInputs
end Sieve
