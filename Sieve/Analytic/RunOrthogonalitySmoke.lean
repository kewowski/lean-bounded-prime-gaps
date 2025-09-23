/-
  Sieve/Analytic/RunOrthogonalitySmoke.lean
  Tiny smoke test that exercises the residue-indicator orthogonality field
  from `BVToolbox`. No heavy imports; keeps the repo green.
-/
import Mathlib
import Sieve.Analytic.LargeSieveCore

noncomputable section
open Classical BigOperators

namespace Sieve
namespace Analytic

variable (T : BVToolbox) {q n m : ℕ}

/-- Smoke test wrapper for `BVToolbox.orthogonality_residueIndicators`. -/
theorem demo_orthogonality :
    (∑ r : ZMod q.succ,
        (if ((n : ZMod q.succ) = r) then (1 : ℝ) else 0) *
        (if ((m : ZMod q.succ) = r) then (1 : ℝ) else 0))
  = (if ((n : ZMod q.succ) = (m : ZMod q.succ)) then (1 : ℝ) else 0) :=
by
  simpa using (T.orthogonality_residueIndicators (q := q) (n := n) (m := m))

end Analytic
end Sieve
