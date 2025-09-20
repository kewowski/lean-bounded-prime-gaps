import Mathlib
import MaynardTao.WeightsAPI
import MaynardTao.Sums
import MaynardTao.ShiftPrimes
import MaynardTao.PrimeCounts

/-!
# MaynardTao.BoundedGaps

A small spec bundle plus convenient accessors for the
Maynard–Tao pipeline. No imports of `Inequalities` here to avoid cycles.
-/

namespace MaynardTao
namespace BoundedGaps

/-- Specification bundle for a bounded-gaps run. -/
structure Spec where
  P      : WeightParams
  W      : SieveWeight P
  N      : ℕ
  lambda : ℚ := 0    -- target advantage factor (to be supplied by analysis/numerics)

namespace Spec

/-- Convenience: the admissible tuple. -/
def H (s : Spec) : Finset ℤ := s.P.H

/-- Baseline mass `S0`. -/
def S0 (s : Spec) : ℚ := Sums.S0 (W := s.W) s.N

/-- Shifted-prime mass `S'`. -/
noncomputable def Sprime (s : Spec) : ℚ :=
  ShiftPrimes.S_prime (W := s.W) s.N s.P.H

/-- Maynard–Tao criterion in its simplest inequality form. -/
noncomputable def criterion (s : Spec) : Prop :=
  s.Sprime ≥ s.lambda * s.S0

/-- Replace `s.lambda` by a chosen value. -/
def withLambda (s : Spec) (lam : ℚ) : Spec :=
  { s with lambda := lam }

@[simp] lemma withLambda_P (s : Spec) (lam : ℚ) :
    (s.withLambda lam).P = s.P := rfl

@[simp] lemma withLambda_W (s : Spec) (lam : ℚ) :
    (s.withLambda lam).W = s.W := rfl

@[simp] lemma withLambda_N (s : Spec) (lam : ℚ) :
    (s.withLambda lam).N = s.N := rfl

@[simp] lemma withLambda_H (s : Spec) (lam : ℚ) :
    (s.withLambda lam).H = s.H := rfl

@[simp] lemma withLambda_S0 (s : Spec) (lam : ℚ) :
    (s.withLambda lam).S0 = s.S0 := rfl

@[simp] lemma withLambda_Sprime (s : Spec) (lam : ℚ) :
    (s.withLambda lam).Sprime = s.Sprime := rfl

@[simp] lemma withLambda_lambda (s : Spec) (lam : ℚ) :
    (s.withLambda lam).lambda = lam := rfl

end Spec
end BoundedGaps
end MaynardTao
namespace MaynardTao
namespace BoundedGaps
namespace Spec

/-- Baseline mass is nonnegative. -/
lemma S0_nonneg (s : Spec) : 0 ≤ s.S0 := by
  classical
  unfold Spec.S0
  exact Sums.S0_nonneg (W := s.W) s.N

/-- Shifted-prime mass is nonnegative. -/
lemma Sprime_nonneg (s : Spec) : 0 ≤ s.Sprime := by
  classical
  simpa [Spec.Sprime] using
    ShiftPrimes.S_prime_nonneg (W := s.W) s.N s.P.H

end Spec
end BoundedGaps
end MaynardTao
