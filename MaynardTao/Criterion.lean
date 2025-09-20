import Mathlib
import MaynardTao.BoundedGaps
import MaynardTao.Sums
import MaynardTao.PrimeCounts
import MaynardTao.Bridging

/-!
MaynardTao/Criterion.lean
-------------------------
A small wrapper that packages the standard Maynard–Tao criterion:

Assumption:
  S_{≥ r} ≥ θ · S₀

Conclusion:
  S' ≥ (r : ℚ) · θ · S₀

This just re-exports `Bridging.criterion_from_theta` with a clean interface.
-/

namespace MaynardTao
namespace Criterion

/-- The numerical assumption typically verified by optimization. -/
def Assumption (s : BoundedGaps.Spec) (r : ℕ) (θ : ℚ) : Prop :=
  PrimeCounts.S_atLeast (W := s.W) s.N s.P.H r
    ≥ θ * Sums.S0 (W := s.W) s.N

/-- The target inequality used to deduce many-primes conclusions. -/
def Conclusion (s : BoundedGaps.Spec) (r : ℕ) (θ : ℚ) : Prop :=
  s.Sprime ≥ (r : ℚ) * θ * s.S0

/-- The criterion: if `Assumption s r θ`, then `Conclusion s r θ`. -/
theorem result (s : BoundedGaps.Spec) (r : ℕ) (θ : ℚ)
    (hθ : Assumption s r θ) : Conclusion s r θ := by
  dsimp [Assumption, Conclusion] at hθ ⊢
  exact Bridging.criterion_from_theta s r θ hθ

end Criterion
end MaynardTao
