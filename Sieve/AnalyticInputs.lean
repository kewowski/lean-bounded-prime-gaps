/-
  Sieve/AnalyticInputs.lean
  Minimal, stable interface for analytic inputs (average window-hit lower bounds).
  This is a thin alias of the contract used by Stage-3 bridge lemmas.
-/
import Sieve.AnalyticBridge

set_option linter.unusedVariables false

namespace Sieve
namespace AnalyticInputs

/-- Public alias for the analytic average-lower-bound contract. -/
abbrev AvgWindowHitLB := Sieve.Analytic.AvgWindowHitLB

/-- Convenience constructor: same as the underlying structure fields. -/
@[inline] def mk
  (lower :
      ∀ (W : Sieve.MaynardWeights.Weight) (τ : ℝ)
        (H : Finset ℤ) (HS : Sieve.Stage3.HitSystem),
        (Sieve.MTCore.heavySet W τ).Nonempty → ℝ)
  (le_avg :
      ∀ (W : Sieve.MaynardWeights.Weight) (τ : ℝ)
        (H : Finset ℤ) (HS : Sieve.Stage3.HitSystem)
        (hne : (Sieve.MTCore.heavySet W τ).Nonempty),
        lower W τ H HS hne
          ≤ Sieve.Stage3.avgOver (Sieve.MTCore.heavySet W τ)
              (Sieve.Stage3.windowSum H (Sieve.Stage3.hitIndicator HS)))
  : AvgWindowHitLB :=
{ lower := lower, le_avg := le_avg }

end AnalyticInputs
end Sieve

