import Mathlib
import MaynardTao.BoundedGaps
import MaynardTao.Inequalities
import MaynardTao.SpecGlue
import MaynardTao.Sums
import MaynardTao.PrimeCounts

/-!
MaynardTao/SpecDemo.lean
------------------------
A minimal template: if you can prove a lower bound on `S_{≥ r}`,
`RCritSpec_all` + glue gives `criterion` for `s.withLambda ((r:ℚ)*θ)`.
-/

namespace MaynardTao
namespace BoundedGaps
namespace Spec

/-- Template: from a lower bound on `S_{≥ r}` to `criterion` via `RCritSpec_all`. -/
lemma criterion_from_RCrit_all_and_lower
    (s : Spec) (r : ℕ) (θ : ℚ)
    (hLower : θ * Sums.S0 (W := s.W) s.N ≤
              PrimeCounts.S_atLeast (W := s.W) s.N s.P.H r) :
    criterion (s.withLambda ((r : ℚ) * θ)) := by
  classical
  -- global Maynard–Tao inequality
  have hRCrit : MaynardTao.Inequalities.RCritSpec s r :=
    MaynardTao.Inequalities.RCritSpec_all s r
  -- glue to the Spec-level criterion
  exact criterion_withLambda_of_RCrit_and_lower s r θ hRCrit hLower

end Spec
end BoundedGaps
end MaynardTao
