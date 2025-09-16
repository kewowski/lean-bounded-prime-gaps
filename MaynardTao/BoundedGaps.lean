import Mathlib
import MaynardTao.AdmissibleTuples
import MaynardTao.WeightsAPI
import MaynardTao.WeightOps
import MaynardTao.Sums
import MaynardTao.ShiftPrimes
import MaynardTao.Params

/-!
MaynardTao/BoundedGaps.lean
---------------------------
A lightweight, proof-free specification layer for bounded gaps.

It packages together:
* Parameters `P : WeightParams`
* A concrete nonnegative sieve weight `W : SieveWeight P`
* A cutoff `N : ℕ`
and defines the key functionals we will later bound:

* `S0`      : baseline mass up to `N`
* `Sprime`  : sum over shifts `h ∈ P.H` of weighted primes `n + h`
* `criterion` : a Maynard–Tao style inequality `Sprime ≥ lambda * S0`

No theorems here; this is an API target other modules can depend on without `sorry`.
-/

namespace MaynardTao
namespace BoundedGaps

/-- Specification bundle for a bounded-gaps run. -/
structure Spec where
  P    : WeightParams
  W    : SieveWeight P
  N    : ℕ
  lambda : ℚ := 0    -- target advantage factor (to be supplied by analysis/numerics)

namespace Spec

/-- Convenience: the admissible tuple. -/
def H (s : Spec) : Finset ℤ := s.P.H

/-- Baseline mass `S0`. -/
def S0 (s : Spec) : ℚ := Sums.S0 (W := s.W) s.N

/-- Shifted-prime mass `Sprime`. -/
noncomputable def Sprime (s : Spec) : ℚ :=
  ShiftPrimes.S_prime (W := s.W) s.N s.P.H

/-- Maynard–Tao criterion in its simplest inequality form. -/
noncomputable def criterion (s : Spec) : Prop :=
  s.Sprime ≥ s.lambda * s.S0

/-- Sanity: both `S0` and `Sprime` are nonnegative (immediate from earlier lemmas). -/
lemma S0_nonneg (s : Spec) : 0 ≤ s.S0 := by
  classical
  unfold S0
  exact Sums.S0_nonneg (W := s.W) s.N

lemma Sprime_nonneg (s : Spec) : 0 ≤ s.Sprime := by
  classical
  unfold Sprime
  exact ShiftPrimes.S_prime_nonneg (W := s.W) s.N s.P.H

/-- Update `lambda` without touching `P`, `W`, or `N`. -/
def withLambda (s : Spec) (lam : ℚ) : Spec :=
  { s with lambda := lam }

@[simp] lemma H_withLambda (s : Spec) (lam : ℚ) : (s.withLambda lam).H = s.H := rfl
@[simp] lemma S0_withLambda (s : Spec) (lam : ℚ) : (s.withLambda lam).S0 = s.S0 := rfl
@[simp] lemma Sprime_withLambda (s : Spec) (lam : ℚ) : (s.withLambda lam).Sprime = s.Sprime := rfl
@[simp] lemma criterion_withLambda (s : Spec) (lam : ℚ) :
    (s.withLambda lam).criterion ↔ s.Sprime ≥ lam * s.S0 := Iff.rfl

end Spec

end BoundedGaps
end MaynardTao
