/-
  Sieve/Analytic/RunPartialSummationSmoke.lean
  Minimal touch: keep the PartialSummationBound interface in the build graph
  without committing to a specific inequality shape.
-/
import Sieve.Analytic.BVToolboxSpec

namespace Sieve
namespace Analytic

/-- Touch `ps.N` and `ps.bound` so signature drift trips early. -/
theorem runPartialSummationSmoke_touch (T : BVToolbox) : True := by
  let _N : ℕ := T.ps.N
  let _b := T.ps.bound
  exact trivial

end Analytic
end Sieve
