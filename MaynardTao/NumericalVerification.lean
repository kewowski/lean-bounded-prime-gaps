import Mathlib
import MaynardTao.BoundedGaps
import MaynardTao.Scenarios

/-!
MaynardTao/NumericalVerification.lean
-------------------------------------
A lightweight verification shim:

* `ratio s`              : Sprime / S0 with a safe 0 guard.
* `criterion_zero_lambda`: the criterion holds when lambda = 0.
* `trivialSpecCriterion` : instantiate the criterion for a trivial spec.
No `sorry`.
-/

namespace MaynardTao
namespace NumericalVerification

open BoundedGaps

/-- Safe ratio `Sprime / S0` with `0` when `S0 = 0`. -/
noncomputable def ratio (s : Spec) : ℚ :=
  if s.S0 = 0 then 0 else s.Sprime / s.S0

/-- The Maynard–Tao inequality is trivially true when `lambda = 0`. -/
lemma criterion_zero_lambda (s : Spec) :
    (s.withLambda 0).criterion := by
  -- goal: s.Sprime ≥ 0 * s.S0, which follows from nonnegativity of `Sprime`
  simpa [Spec.criterion, Spec.withLambda, zero_mul] using s.Sprime_nonneg

/-- Check the criterion for the trivial spec with given `N, c, lambda`. -/
noncomputable def trivialSpecCriterion (N : ℕ) (c : ℚ) (hc : 0 < c) (lam : ℚ) : Prop :=
  let s := Scenarios.trivialSpec N c hc
  (s.withLambda lam).criterion

end NumericalVerification
end MaynardTao
