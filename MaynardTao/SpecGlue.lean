import Mathlib
import MaynardTao.BoundedGaps
import MaynardTao.Inequalities
import MaynardTao.Sums
import MaynardTao.PrimeCounts
import MaynardTao.ShiftPrimes

/-!
MaynardTao/SpecGlue.lean
------------------------
Glue from the Maynard–Tao inequality and a density/lower-bound
on `S_atLeast` to the `BoundedGaps.Spec.criterion`.
-/

namespace MaynardTao
namespace BoundedGaps
namespace Spec

open Inequalities

/-- If `S' ≥ r * S_{≥ r}` and `θ * S0 ≤ S_{≥ r}`, then
    `S' ≥ (r*θ) * S0`, i.e. the Spec's `criterion` with `lambda = r*θ`. -/
lemma criterion_of_RCrit_and_lower
    (s : Spec) (r : ℕ) (θ : ℚ)
    (h1 : Inequalities.RCritSpec s r)
    (h2 : θ * Sums.S0 (W := s.W) s.N ≤
          PrimeCounts.S_atLeast (W := s.W) s.N s.P.H r) :
    s.Sprime ≥ (r : ℚ) * θ * s.S0 := by
  classical
  -- From RCrit: S' ≥ r * S_{≥ r}
  have hR : s.Sprime ≥ (r : ℚ) * PrimeCounts.S_atLeast (W := s.W) s.N s.P.H r := by
    simpa [Inequalities.RCritSpec] using h1
  -- Monotonicity: multiply the lower bound `θ * S0 ≤ S_{≥ r}` by `(r:ℚ) ≥ 0`
  have hr_nonneg : 0 ≤ (r : ℚ) := by exact_mod_cast (Nat.zero_le r)
  have hpush :
      (r : ℚ) * (θ * Sums.S0 (W := s.W) s.N)
        ≤ (r : ℚ) * PrimeCounts.S_atLeast (W := s.W) s.N s.P.H r :=
    mul_le_mul_of_nonneg_left h2 hr_nonneg
  -- Chain inequalities and tidy associativity/commutativity:
  have : (r : ℚ) * θ * s.S0 ≤ (r : ℚ) * PrimeCounts.S_atLeast (W := s.W) s.N s.P.H r := by
    simpa [mul_assoc, mul_comm, mul_left_comm, Spec.S0] using hpush
  exact le_trans this hR

end Spec
end BoundedGaps
end MaynardTao
namespace MaynardTao
namespace BoundedGaps
namespace Spec

/-- Glue: if `S' ≥ r·S_{≥r}` and `theta·S0 ≤ S_{≥r}`, then
    `criterion` holds for `s.withLambda ((r:ℚ)·theta)`. -/
lemma criterion_withLambda_of_RCrit_and_lower
    (s : Spec) (r : ℕ) (theta : ℚ)
    (h1 : MaynardTao.Inequalities.RCritSpec s r)
    (h2 : theta * Sums.S0 (W := s.W) s.N ≤
          PrimeCounts.S_atLeast (W := s.W) s.N s.P.H r) :
    criterion (s.withLambda ((r : ℚ) * theta)) := by
  classical
  -- From RCrit: S' ≥ r * S_{≥ r}
  have hR : s.Sprime ≥ (r : ℚ) * PrimeCounts.S_atLeast (W := s.W) s.N s.P.H r := by
    simpa [MaynardTao.Inequalities.RCritSpec] using h1
  -- Push the lower bound by multiplying with (r:ℚ) ≥ 0
  have hr_nonneg : 0 ≤ (r : ℚ) := by exact_mod_cast (Nat.zero_le r)
  have hpush :
      (r : ℚ) * (theta * Sums.S0 (W := s.W) s.N)
        ≤ (r : ℚ) * PrimeCounts.S_atLeast (W := s.W) s.N s.P.H r :=
    mul_le_mul_of_nonneg_left h2 hr_nonneg
  -- Tidy and chain to `criterion` on `withLambda`
  have : s.Sprime ≥ (r : ℚ) * theta * s.S0 := by
    have hL :
      (r : ℚ) * theta * s.S0 ≤ (r : ℚ) * PrimeCounts.S_atLeast (W := s.W) s.N s.P.H r := by
      simpa [mul_assoc, mul_comm, mul_left_comm, Spec.S0] using hpush
    exact le_trans hL hR
  -- Now rewrite `criterion` for `withLambda` and finish
  dsimp [criterion, withLambda, Spec.Sprime, Spec.S0] at this ⊢
  simpa [mul_assoc, mul_comm, mul_left_comm]

end Spec
end BoundedGaps
end MaynardTao
