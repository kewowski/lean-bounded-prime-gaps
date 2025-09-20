/-
  Sieve/RunStage3WindowDemo.lean
  Smoke test for Stage-3 window average → witness.
-/
import Sieve.Stage3Window
import Sieve.ConstWeight  -- just to have a Weight around

noncomputable section
open Classical BigOperators

-- pick any weight W; the lemma works for any set, not using properties of W beyond the set
example (W : Sieve.MaynardWeights.Weight) (τ : ℝ)
    (hne : (Sieve.MTCore.heavySet W τ).Nonempty) :
    let H : Finset ℤ := ([0, 2] : List ℤ).toFinset
    let f : ℤ → ℝ := fun _ => 1
    ∃ n ∈ Sieve.MTCore.heavySet W τ,
      Sieve.Stage3.avgOver (Sieve.MTCore.heavySet W τ) (Sieve.Stage3.windowSum H f)
        ≤ Sieve.Stage3.windowSum H f n := by
  intro H f
  simpa using
    Sieve.Stage3.exists_heavy_with_window_ge_avg (W := W) (τ := τ)
      (H := H) (f := f) hne
