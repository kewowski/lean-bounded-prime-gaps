/-
  Sieve/RunStage2ThresholdsSecondDemo.lean
  Demo: second-moment heavy-hit bound for constant weights.
-/
import Mathlib
import Sieve.ConstWeight
import Sieve.MTMoments
import Sieve.Stage2Thresholds

noncomputable section
open Classical

namespace Sieve.RunStage2ThresholdsSecondDemo

def window (M : ℕ) : Finset ℤ := Finset.Icc (-(M : ℤ)) (M : ℤ)

/-- For any τ>0: count{w ≥ τ} ≤ secondMoment / τ^2. -/
example (M : ℕ) (c τ : ℝ) (hc : 0 ≤ c) (hτ : 0 < τ) :
    (( (Sieve.ConstWeight.const (window M) c hc).support.filter
        (fun n => τ ≤ (Sieve.ConstWeight.const (window M) c hc).w n) ).card : ℝ)
      ≤ Sieve.MTMoments.secondMoment (Sieve.ConstWeight.const (window M) c hc)
        / τ^2 :=
  Sieve.Stage2.heavy_count_le_of_secondMoment
    (Sieve.ConstWeight.const (window M) c hc) hτ

end Sieve.RunStage2ThresholdsSecondDemo
