/-
  Sieve/Analytic/ResidueScaling.lean
  Constant (ℂ) scaling lemmas for `residueSum`.
-/
import Mathlib
import Sieve.Analytic.ResidueSumBasics

noncomputable section
open Classical BigOperators

namespace Sieve
namespace Analytic

/--
Pull out a constant complex factor from the `residueSum`.
-/
theorem residueSum_const_mul_left
    (a : ℕ → ℂ) (c : ℂ) (N q : ℕ) (r : ZMod q.succ) :
    residueSum (fun n => c * a n) N q r
      = c * residueSum a N q r := by
  classical
  unfold residueSum
  -- Push `c` across the indicator inside the summand.
  have h :
      (∑ n ∈ Finset.Icc 1 N,
          (if ((n : ZMod q.succ) = r) then c * a n else 0))
        =
      (∑ n ∈ Finset.Icc 1 N,
          (c * (if ((n : ZMod q.succ) = r) then a n else 0))) := by
    refine Finset.sum_congr rfl ?_
    intro n _; by_cases h : ((n : ZMod q.succ) = r)
    · simp [h]
    · simp [h]
  -- Factor `c` out of the sum.
  have hfactor :
      (∑ n ∈ Finset.Icc 1 N, c * (if ((n : ZMod q.succ) = r) then a n else 0))
        = c * (∑ n ∈ Finset.Icc 1 N, (if ((n : ZMod q.succ) = r) then a n else 0)) := by
    simpa using
      (Finset.mul_sum (a := c)
        (s := Finset.Icc 1 N)
        (f := fun n => (if ((n : ZMod q.succ) = r) then a n else 0))).symm
  simpa [h, hfactor]

/--
Right-constant scaling variant (uses commutativity of `ℂ` multiplication).
-/
theorem residueSum_mul_const_right
    (a : ℕ → ℂ) (c : ℂ) (N q : ℕ) (r : ZMod q.succ) :
    residueSum (fun n => a n * c) N q r
      = c * residueSum a N q r := by
  classical
  -- Rewrite to the left-constant form and reuse the previous lemma.
  simpa [mul_comm] using
    (residueSum_const_mul_left a c N q r)

end Analytic
end Sieve
