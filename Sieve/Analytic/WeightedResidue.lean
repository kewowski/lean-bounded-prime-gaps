/-
  Sieve/Analytic/WeightedResidue.lean
  Weighted residue sums and a constant-weight factorization lemma.
-/
import Mathlib
import Sieve.Analytic.ResidueSumBasics

noncomputable section
open Classical BigOperators

namespace Sieve
namespace Analytic

/-- Weighted residue sum:
    `∑_{n=1}^N 1_{n≡r (mod q+1)} · (w n) · a n`. -/
def residueSumW (a : ℕ → ℂ) (w : ℕ → ℝ) (N q : ℕ) (r : ZMod q.succ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N,
    if ((n : ZMod q.succ) = r) then ((w n : ℂ) * a n) else 0

/-- For constant weights `w n ≡ c`, the weight factors out. -/
theorem residueSumW_const_weight
    (a : ℕ → ℂ) (c : ℝ) (N q : ℕ) (r : ZMod q.succ) :
    residueSumW a (fun _ => c) N q r
      = (c : ℂ) * residueSum a N q r := by
  classical
  unfold residueSumW residueSum
  -- Pull the constant through the indicator, pointwise in the summand.
  have h1 :
      (∑ n ∈ Finset.Icc 1 N,
          (if ((n : ZMod q.succ) = r) then ((c : ℂ) * a n) else 0))
        =
      (∑ n ∈ Finset.Icc 1 N,
          ((c : ℂ) * (if ((n : ZMod q.succ) = r) then a n else 0))) := by
    refine Finset.sum_congr rfl ?_
    intro n _; by_cases h : ((n : ZMod q.succ) = r)
    · simp [h, mul_comm]
    · simp [h]
  -- Factor `(c : ℂ)` out of the sum.
  have h2 :
      (∑ n ∈ Finset.Icc 1 N,
          ((c : ℂ) * (if ((n : ZMod q.succ) = r) then a n else 0)))
        =
      (c : ℂ) * (∑ n ∈ Finset.Icc 1 N,
          (if ((n : ZMod q.succ) = r) then a n else 0)) := by
    -- `Finset.mul_sum`:  a * ∑ f = ∑ a * f
    simpa using
      (Finset.mul_sum (a := (c : ℂ))
        (s := Finset.Icc 1 N)
        (f := fun n => (if ((n : ZMod q.succ) = r) then a n else 0))).symm
  -- Finish the calculation.
  calc
    (∑ n ∈ Finset.Icc 1 N,
        (if ((n : ZMod q.succ) = r) then ((c : ℂ) * a n) else 0))
        = (∑ n ∈ Finset.Icc 1 N,
            ((c : ℂ) * (if ((n : ZMod q.succ) = r) then a n else 0))) := h1
    _ = (c : ℂ) * (∑ n ∈ Finset.Icc 1 N,
            (if ((n : ZMod q.succ) = r) then a n else 0)) := h2
    _ = (c : ℂ) * (residueSum a N q r) := by
          -- Avoid any cancellation: just unfold and `rfl`.
          change (c : ℂ) *
            (∑ n ∈ Finset.Icc 1 N, (if ((n : ZMod q.succ) = r) then a n else 0))
            = (c : ℂ) *
            (∑ n ∈ Finset.Icc 1 N, (if ((n : ZMod q.succ) = r) then a n else 0))
          rfl

end Analytic
end Sieve
