/-
  Sieve/RunStage2FirstMomentEmptyDemo.lean
  Smoke test: first-moment emptiness criterion.
-/
import Sieve.Stage2Exports

noncomputable section
open Classical BigOperators

example (W : Sieve.MaynardWeights.Weight) (M τ : ℝ)
    (hτpos : 0 < τ)
    (h_first : (∑ n ∈ W.support, W.w n) ≤ (W.support.card : ℝ) * M)
    (hlt : (W.support.card : ℝ) * M / τ < 1) :
    (W.support.filter (fun n => τ ≤ W.w n)).card = 0 := by
  simpa using
    Sieve.Stage2.heavy_nonstrict_empty_of_firstMoment_lt
      (W := W) (M := M) (τ := τ) hτpos h_first hlt
