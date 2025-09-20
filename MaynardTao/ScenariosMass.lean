import Mathlib
import MaynardTao.BoundedGaps
import MaynardTao.NumericLower
import MaynardTao.PrimeCounts
import MaynardTao.Sums

/-!
MaynardTao/ScenariosMass.lean
-----------------------------
A lightweight scenario: assume a weighted mass lower bound for
the event `atLeast H r`, then conclude the `criterion` for
`withLambda ((r:ℚ) * θ)` via our glue.
-/

namespace MaynardTao
namespace ScenariosMass

open BoundedGaps

/-- A scenario packaged as "we have a mass lower bound at level `r`". -/
structure Scenario where
  s    : BoundedGaps.Spec
  r    : ℕ
  θ    : ℚ
  hmass :
    ∑ n ∈ (s.W.restrict s.N).support,
        (s.W.restrict s.N).w n *
          MaynardTao.cIndicator (PrimeCounts.atLeast s.P.H r n)
    ≥
    θ * ∑ n ∈ (s.W.restrict s.N).support, (s.W.restrict s.N).w n

/-- From the packaged mass bound, conclude the Spec-level criterion. -/
theorem criterion (X : Scenario) :
    BoundedGaps.Spec.criterion (X.s.withLambda ((X.r : ℚ) * X.θ)) := by
  classical
  exact MaynardTao.NumericLower.criterion_from_RCrit_all_and_mass
          X.s X.r (θ := X.θ) X.hmass

end ScenariosMass
end MaynardTao
