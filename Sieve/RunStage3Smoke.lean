/-
  Sieve/RunStage3Smoke.lean
  Smoke test using Stage-3 exports.
-/
import Sieve.Stage3Exports

noncomputable section
open Classical BigOperators

example (W : Sieve.MaynardWeights.Weight) (M τ : ℝ)
    (hpos : 0 < W.support.card) (hτpos : 0 < τ)
    (h_first : (∑ n ∈ W.support, W.w n) ≤ (W.support.card : ℝ) * M)
    (hτleavg : τ ≤ (∑ m ∈ W.support, W.w m) / (W.support.card : ℝ)) :
    True := by
  have _ := Sieve.Stage3.heavyDensity_le_of_firstMoment_MT (W := W) (M := M) (τ := τ)
                hpos hτpos h_first
  have _ := Sieve.Stage3.heavyDensity_le_of_secondMoment_MT (W := W) (τ := τ)
                hpos hτpos
  have _ := Sieve.Stage3.heavySet_nonempty_of_avg_ge (W := W) (τ := τ)
                hpos hτleavg
  have _ := Sieve.Stage3.one_le_heavy_count_real_of_avg_ge (W := W) (τ := τ)
                hpos hτleavg
  exact True.intro
