import Mathlib
import Sieve.ConstWeight
import Sieve.ConstWeightLemmas
import Sieve.MTMoments
/-
  Sieve/ConstWeightSimp.lean
  `[simp]` lemmas for sums over a constant weight's support (c and c^2 cases).
-/

noncomputable section
open Classical

namespace Sieve.ConstWeight

@[simp] lemma sum_w_const
    (supp : Finset ℤ) (c : ℝ) (hc : 0 ≤ c) :
    (∑ n ∈ (const supp c hc).support, (const supp c hc).w n)
      = (supp.card : ℝ) * c := by
  simpa [Sieve.MTMoments.firstMoment_sum_repr] using
    Sieve.ConstWeight.firstMoment_const supp c hc

@[simp] lemma sum_w_sq_const
    (supp : Finset ℤ) (c : ℝ) (hc : 0 ≤ c) :
    (∑ n ∈ (const supp c hc).support, ((const supp c hc).w n)^2)
      = (supp.card : ℝ) * c^2 := by
  simpa [Sieve.MTMoments.secondMoment_sum_repr] using
    Sieve.ConstWeight.secondMoment_const supp c hc

end Sieve.ConstWeight
/-
  Extra c = 1 simp lemmas so `Sieve.Run` closes goals automatically.
-/

noncomputable section
open Classical

namespace Sieve.ConstWeight

@[simp] lemma sum_w_const_one
    (supp : Finset ℤ) (hc : 0 ≤ (1 : ℝ)) :
    (∑ n ∈ (const supp 1 hc).support, (const supp 1 hc).w n)
      = (supp.card : ℝ) := by
  simpa [one_mul, mul_one] using
    (sum_w_const supp 1 hc)

@[simp] lemma sum_w_sq_const_one
    (supp : Finset ℤ) (hc : 0 ≤ (1 : ℝ)) :
    (∑ n ∈ (const supp 1 hc).support, ((const supp 1 hc).w n)^2)
      = (supp.card : ℝ) := by
  -- c = 1 so c^2 = 1
  simpa [pow_two, one_mul, mul_one] using
    (sum_w_sq_const supp 1 hc)

end Sieve.ConstWeight
/-
  Extra c = 1 moment simp lemmas so `Sieve.Run` closes goals automatically.
-/

noncomputable section
open Classical

namespace Sieve.ConstWeight

@[simp] lemma firstMoment_const_one
    (supp : Finset ℤ) (hc : 0 ≤ (1 : ℝ)) :
    Sieve.MTMoments.firstMoment (const supp 1 hc) = (supp.card : ℝ) := by
  simpa [one_mul, mul_one] using
    (Sieve.ConstWeight.firstMoment_const supp 1 hc)

@[simp] lemma secondMoment_const_one
    (supp : Finset ℤ) (hc : 0 ≤ (1 : ℝ)) :
    Sieve.MTMoments.secondMoment (const supp 1 hc) = (supp.card : ℝ) := by
  -- c = 1 so c^2 = 1
  simpa [pow_two, one_mul, mul_one] using
    (Sieve.ConstWeight.secondMoment_const supp 1 hc)

end Sieve.ConstWeight

