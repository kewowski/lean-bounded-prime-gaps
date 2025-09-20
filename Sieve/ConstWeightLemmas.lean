/-
  Sieve/ConstWeightLemmas.lean
  Exact moment formulas for the constant-weight builder.
-/
import Mathlib
import Sieve.ConstWeight
import Sieve.MTMoments

noncomputable section
open Classical
open Sieve.MaynardWeights
open Sieve.MTMoments

namespace Sieve.ConstWeight

/-- First moment of the constant weight `const supp c` is `(supp.card : ℝ) * c`. -/
lemma firstMoment_const (supp : Finset Int) (c : ℝ) (hc : 0 ≤ c) :
    firstMoment (const supp c hc) = (supp.card : ℝ) * c := by
  classical
  simp [firstMoment, const, Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- Second moment of the constant weight `const supp c` is `(supp.card : ℝ) * c^2`. -/
lemma secondMoment_const (supp : Finset Int) (c : ℝ) (hc : 0 ≤ c) :
    secondMoment (const supp c hc) = (supp.card : ℝ) * c^2 := by
  classical
  simp [secondMoment, const, Finset.sum_const, nsmul_eq_mul, mul_comm, pow_two]

end Sieve.ConstWeight
