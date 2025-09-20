/-
  Sieve/RunStage2SquaredDemo.lean
  Smoke test for the squared-average glue bound.
-/
import Sieve.Stage2Exports

noncomputable section
open Classical BigOperators

example (W : Sieve.MaynardWeights.Weight) (M : ℝ)
    (h_first : (∑ n ∈ W.support, W.w n) ≤ (W.support.card : ℝ) * M) :
    (Sieve.MTMoments.firstMoment W) ^ 2
      ≤ (W.support.card : ℝ) ^ 2 * M ^ 2 := by
  simpa using
    Sieve.Stage2.first_sq_le_card_sq_mul_M_sq (W := W) (M := M) h_first
