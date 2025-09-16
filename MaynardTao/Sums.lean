import Mathlib
import MaynardTao.WeightsAPI
import MaynardTao.WeightOps

/-!
MaynardTao/Sums.lean
--------------------
Lightweight sum/indicator utilities for Maynard–Tao style weights.

* `indicator` : ℚ-valued indicator for a decidable proposition.
* `cIndicator`: same, but always using classical decidability (noncomputable).
* `S0 W N`    : baseline sum of a weight restricted to `n ≤ N`.
* `S_of`      : weighted sum against a predicate `φ : ℕ → Prop` (noncomputable).
* `indicator_nonneg`, `cIndicator_nonneg`, `S0_nonneg`, `S_of_nonneg`.
No `sorry`.
-/

namespace MaynardTao

open scoped BigOperators

/-- Rational-valued indicator of a decidable proposition. -/
def indicator (b : Prop) [Decidable b] : ℚ := if b then 1 else 0

@[simp] lemma indicator_true : indicator True = (1 : ℚ) := by
  simp [indicator]

@[simp] lemma indicator_false : indicator False = (0 : ℚ) := by
  simp [indicator]

/-- The indicator is always nonnegative. -/
lemma indicator_nonneg (b : Prop) [Decidable b] : 0 ≤ indicator b := by
  by_cases hb : b
  · simp [indicator, hb]
  · simp [indicator, hb]

/-- Classical indicator: same as `indicator` but always uses classical decidability. -/
noncomputable def cIndicator (b : Prop) : ℚ := by
  classical exact indicator b

@[simp] lemma cIndicator_true : cIndicator True = (1 : ℚ) := by
  classical
  simp [cIndicator, indicator]

@[simp] lemma cIndicator_false : cIndicator False = (0 : ℚ) := by
  classical
  simp [cIndicator, indicator]

lemma cIndicator_nonneg (b : Prop) : 0 ≤ cIndicator b := by
  classical
  simpa [cIndicator] using indicator_nonneg b

namespace Sums

variable {P : WeightParams}

/-- Baseline sum `S0`: total mass of `W` restricted to `n ≤ N`. -/
def S0 (W : SieveWeight P) (N : ℕ) : ℚ :=
  (W.restrict N).total

/-- Generic weighted sum against a predicate `φ : ℕ → Prop`.
We use classical decidability for propositions, so this is noncomputable. -/
noncomputable def S_of (W : SieveWeight P) (N : ℕ) (φ : ℕ → Prop) : ℚ := by
  classical
  exact ∑ n ∈ (W.restrict N).support, (W.restrict N).w n * indicator (φ n)

/-- `S0` is nonnegative. -/
lemma S0_nonneg (W : SieveWeight P) (N : ℕ) : 0 ≤ S0 (W := W) N := by
  classical
  unfold S0 SieveWeight.total
  refine Finset.sum_nonneg ?h
  intro n hn
  exact (W.restrict N).nonneg n

/-- `S_of` is nonnegative for any predicate `φ`. -/
lemma S_of_nonneg (W : SieveWeight P) (N : ℕ)
    (φ : ℕ → Prop) : 0 ≤ S_of (W := W) N φ := by
  classical
  unfold S_of
  refine Finset.sum_nonneg ?h
  intro n hn
  have hw : 0 ≤ (W.restrict N).w n := (W.restrict N).nonneg n
  have hi : 0 ≤ indicator (φ n) := indicator_nonneg (φ n)
  exact mul_nonneg hw hi

end Sums

end MaynardTao
