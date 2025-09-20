/-
  Sieve/MTCore.lean
  Stage-3 skeleton: stable interfaces for tuple + weight stats.
-/
import Mathlib
import Sieve.AdmissibleTuples
import Sieve.MaynardWeights
import Sieve.MTMoments

noncomputable section
open Classical BigOperators

namespace Sieve
namespace MTCore

/-- A minimal tuple configuration for MT-style arguments. -/
structure TupleConfig where
  H      : Finset ℤ
  admiss : Sieve.AdmissibleTuples.Admissible H

/-- Basic per-weight stats we commonly thread through Stage 3. -/
structure WeightedStats (W : Sieve.MaynardWeights.Weight) : Type where
  s  : Finset ℤ := W.support
  S1 : ℝ := Sieve.MTMoments.firstMoment W
  S2 : ℝ := Sieve.MTMoments.secondMoment W

/-- Heavy set at threshold `τ`. -/
abbrev heavySet (W : Sieve.MaynardWeights.Weight) (τ : ℝ) : Finset ℤ :=
  W.support.filter (fun n => τ ≤ W.w n)

/-- Heavy-set density at `τ`. -/
abbrev heavyDensity (W : Sieve.MaynardWeights.Weight) (τ : ℝ) : ℝ :=
  (heavySet W τ).card / (W.support.card : ℝ)

end MTCore
end Sieve
