import Mathlib
import MaynardTao.BoundedGaps
import MaynardTao.NumericLower
import MaynardTao.ScenariosMass

namespace MaynardTao
namespace DemoMass

open BoundedGaps

/-- Sanity check: with θ = 0 (which certainly satisfies θ ≤ 0),
    the criterion holds for `s.withLambda 0` for any `r`. -/
lemma criterion_zero_lambda (s : Spec) (r : ℕ) :
    Spec.criterion (s.withLambda 0) := by
  classical
  have hθ : (0 : ℚ) ≤ 0 := by simp
  simpa using
    NumericLower.criterion_from_RCrit_all_and_nonpos s r (θ := 0) hθ

end DemoMass
end MaynardTao
