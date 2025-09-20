import Mathlib
import MaynardTao.BoundedGaps
import MaynardTao.Scenarios
import MaynardTao.NumericalVerification
import MaynardTao.Inequalities

/-!
MaynardTao/Master.lean
----------------------
Top-level shim that re-exports simple smoke tests:

* `trivial_zero_lambda_holds` — for the trivial spec (empty admissible tuple and a
  positive constant weight), the Maynard–Tao criterion holds when `lambda = 0`.
* `trivial_RCrit_zero` — the `r=0` inequality target holds for the trivial spec.
-/

namespace MaynardTao
namespace Master

open BoundedGaps
open Scenarios
open NumericalVerification
open Inequalities

/-- Smoke test: the inequality is trivially true at `lambda = 0`. -/
theorem trivial_zero_lambda_holds (N : ℕ) (c : ℚ) (hc : 0 < c) :
    ((Scenarios.trivialSpec N c hc).withLambda 0).criterion := by
  simpa using NumericalVerification.criterion_zero_lambda
    (s := Scenarios.trivialSpec N c hc)

/-- Smoke test for the `r=0` target inequality. -/
theorem trivial_RCrit_zero (N : ℕ) (c : ℚ) (hc : 0 < c) :
    Inequalities.RCritSpec (Scenarios.trivialSpec N c hc) 0 := by
  simpa using Inequalities.RCritSpec_zero (s := Scenarios.trivialSpec N c hc)

end Master
end MaynardTao
