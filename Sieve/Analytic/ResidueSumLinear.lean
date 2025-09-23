/-
  Sieve/Analytic/ResidueSumLinear.lean
  Linearity facts for `residueSum` (over ℂ-valued sequences).
  These are safe algebraic helpers with lightweight proofs.

  Results:
    • `residueSum_add`  : residueSum distributes over pointwise addition.
    • `residueSum_neg`  : residueSum of pointwise negation.
    • `residueSum_sub`  : residueSum distributes over subtraction.
    • `[simp] residueSum_zero` : residueSum of the zero function is zero.
-/
import Mathlib
import Sieve.Analytic.ResidueSumBasics

noncomputable section
open Classical BigOperators

namespace Sieve
namespace Analytic

/--
Linearity: `residueSum` distributes over pointwise addition of sequences.
-/
theorem residueSum_add
    (a b : ℕ → ℂ) (N q : ℕ) (r : ZMod q.succ) :
    residueSum (fun n => a n + b n) N q r
      = residueSum a N q r + residueSum b N q r := by
  classical
  unfold residueSum
  have h :
      (fun n : ℕ =>
          if ((n : ZMod q.succ) = r) then (a n + b n) else 0)
        =
      (fun n : ℕ =>
          (if ((n : ZMod q.succ) = r) then a n else 0)
        + (if ((n : ZMod q.succ) = r) then b n else 0)) := by
    funext n; by_cases h : ((n : ZMod q.succ) = r) <;> simp [h]
  simp [h, Finset.sum_add_distrib]

/--
Negation: `residueSum` of the pointwise negative is the negative `residueSum`.
-/
theorem residueSum_neg
    (a : ℕ → ℂ) (N q : ℕ) (r : ZMod q.succ) :
    residueSum (fun n => - a n) N q r
      = - residueSum a N q r := by
  classical
  unfold residueSum
  have h :
      (fun n : ℕ =>
          if ((n : ZMod q.succ) = r) then (- a n) else 0)
        =
      (fun n : ℕ => - (if ((n : ZMod q.succ) = r) then a n else 0)) := by
    funext n; by_cases h : ((n : ZMod q.succ) = r) <;> simp [h]
  simp [h, Finset.sum_neg_distrib]

/--
Subtraction: `residueSum` distributes over pointwise subtraction.
-/
theorem residueSum_sub
    (a b : ℕ → ℂ) (N q : ℕ) (r : ZMod q.succ) :
    residueSum (fun n => a n - b n) N q r
      = residueSum a N q r - residueSum b N q r := by
  classical
  simp [sub_eq_add_neg, residueSum_add, residueSum_neg]

/--
Zero: `residueSum` of the zero sequence is `0`.
-/
@[simp] theorem residueSum_zero
    (N q : ℕ) (r : ZMod q.succ) :
    residueSum (fun _ => (0 : ℂ)) N q r = 0 := by
  classical
  unfold residueSum
  simp

end Analytic
end Sieve
