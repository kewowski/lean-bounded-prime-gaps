/-
  Sieve/Stage2Squared.lean
  RMS/AM-style glue:
  If `firstMoment W ≤ (|support|) * M`, then
  `(firstMoment W)^2 ≤ (|support|)^2 * M^2`.

  Notes:
  • No dependence on Pipeline/Outcome; pass any real `M`.
  • Uses only monotonicity with nonnegativity of moments.
-/
import Mathlib
import Sieve.MaynardWeights
import Sieve.MTMoments

noncomputable section
open Classical BigOperators

namespace Sieve
namespace Stage2

/-- RMS/AM glue: square the average bound safely. -/
theorem rms_am_glue
    (W : Sieve.MaynardWeights.Weight) {M : ℝ}
    (h_first : Sieve.MTMoments.firstMoment W
               ≤ (W.support.card : ℝ) * M) :
    (Sieve.MTMoments.firstMoment W) ^ 2
      ≤ (W.support.card : ℝ) ^ 2 * M ^ 2 := by
  classical
  set a : ℝ := Sieve.MTMoments.firstMoment W
  set b : ℝ := (W.support.card : ℝ) * M
  -- `a ≥ 0` since weights are nonnegative.
  have ha0 : 0 ≤ a := by
    simpa [a, Sieve.MTMoments.firstMoment] using
      Finset.sum_nonneg (by intro n _; exact W.nonneg n)
  -- from `a ≤ b` and `a ≥ 0` we infer `b ≥ 0`.
  have hb0 : 0 ≤ b := le_trans ha0 (by simpa [a, b] using h_first)
  -- Chain: a*a ≤ b*a ≤ b*b  ⇒ a^2 ≤ b^2.
  have h1 : a * a ≤ b * a :=
    mul_le_mul_of_nonneg_right (by simpa [a, b] using h_first) ha0
  have h2 : b * a ≤ b * b :=
    mul_le_mul_of_nonneg_left (by simpa [a, b] using h_first) hb0
  have hsq : a ^ 2 ≤ b ^ 2 := by
    have := le_trans h1 h2
    simpa [pow_two] using this
  -- Expand `b^2 = ((|s|) * M)^2 = (|s|)^2 * M^2`.
  simpa [a, b, pow_two, mul_comm, mul_left_comm, mul_assoc] using hsq

end Stage2
end Sieve
