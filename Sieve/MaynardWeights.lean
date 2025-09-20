/-
  Sieve/MaynardWeights.lean
  UTF-8 (no BOM), ASCII-only.
-/
import Mathlib

noncomputable section
open Classical

namespace Sieve.MaynardWeights

/-- A generic (finitely supported) nonnegative weight on ℤ. -/
structure Weight where
  w        : Int → ℝ
  support  : Finset Int
  nonneg   : ∀ n, 0 ≤ w n
  bounded  : ∃ C : ℝ, 0 ≤ C ∧ ∀ n, |w n| ≤ C
  -- Normalization hooks (to be refined later)
  norm1    : Prop := True
  norm2    : Prop := True

/-- Targets we want the weight to achieve in MT sieve stages. -/
structure WeightTargets where
  firstMomentLower  : ℝ := 0
  secondMomentUpper : ℝ := 0
  dispersionUpper   : ℝ := 0

/-- A packaged constructed weight with achieved targets. -/
structure BuiltWeight where
  base : Weight
  hits : WeightTargets

end Sieve.MaynardWeights
