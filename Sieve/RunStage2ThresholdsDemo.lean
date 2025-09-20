/-
  Sieve/RunStage2ThresholdsDemo.lean
  Smoke test for the Stage-2 Markov (first-moment) heavy-count bound.
-/
import Sieve.Stage2Exports

noncomputable section
open Classical BigOperators

example (W : Sieve.MaynardWeights.Weight) (M τ : ℝ)
    (hτpos : 0 < τ)
    (h_first : (∑ n ∈ W.support, W.w n) ≤ (W.support.card : ℝ) * M) :
    ((W.support.filter (fun n => τ ≤ W.w n)).card : ℝ)
      ≤ (W.support.card : ℝ) * M / τ := by
  simpa using
    Sieve.Stage2.heavy_count_le_of_firstMoment' (W := W) (M := M) (τ := τ)
      hτpos h_first
