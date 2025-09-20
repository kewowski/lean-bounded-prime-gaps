/-
  Sieve/RunStage3MinSmoke.lean
  Smoke test for Stage-3 min bound wrapper.
-/
import Sieve.Stage3Exports

noncomputable section
open Classical BigOperators

example (W : Sieve.MaynardWeights.Weight) (M τ : ℝ)
    (hpos : 0 < W.support.card) (hτpos : 0 < τ)
    (h_first : (∑ n ∈ W.support, W.w n) ≤ (W.support.card : ℝ) * M) :
    True := by
  have _ :=
    Sieve.Stage3.heavyDensity_le_min_MT (W := W) (M := M) (τ := τ)
      hpos hτpos h_first
  exact True.intro
