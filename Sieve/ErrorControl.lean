/-
  Sieve/ErrorControl.lean
  UTF-8 (no BOM), ASCII-only.

  Small reusable inequalities for indicators and weights.
-/

import Mathlib
import Sieve.Weights

open scoped BigOperators

namespace Sieve

/-- Indicator is nonnegative as a Real. -/
lemma indR_nonneg (p : Prop) [Decidable p] : 0 <= indR p := by
  by_cases hp : p <;> simp [indR, hp]

/-- Indicator is at most 1 as a Real. -/
lemma indR_le_one (p : Prop) [Decidable p] : indR p <= 1 := by
  by_cases hp : p <;> simp [indR, hp]

/-- For any real x and any proposition p, `x * indR p ≤ |x|`. -/
lemma mul_indR_le_abs (x : Real) (p : Prop) [Decidable p] :
    x * indR p <= |x| := by
  -- 0 ≤ indR p ≤ 1
  have h0 : 0 <= indR p := indR_nonneg p
  have h1 : indR p <= 1 := indR_le_one p
  -- x ≤ |x|
  have hx' : x <= |x| := le_abs_self x
  -- Multiply by nonneg indR p on the right
  have hxa : x * indR p <= |x| * indR p := by
    simpa using mul_le_mul_of_nonneg_right hx' h0
  -- Use a ≤ 1 to bound |x| * indR p ≤ |x|
  have hnonneg : 0 <= |x| := abs_nonneg _
  have h' := mul_le_mul_of_nonneg_left h1 hnonneg
  have hbound : |x| * indR p <= |x| := by
    simpa [one_mul] using h'
  -- Chain inequalities
  exact le_trans hxa hbound

end Sieve

