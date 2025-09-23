/-
  Sieve/Analytic/ResidueSumVanish.lean
  Vanishing lemmas for `residueSum` in simple scenarios.
-/
import Mathlib
import Sieve.Analytic.ResidueSumBasics

noncomputable section
open Classical BigOperators

namespace Sieve
namespace Analytic

/-- If the window is empty (`N = 0`), the residue sum is `0`. -/
@[simp] theorem residueSum_N_zero (a : ℕ → ℂ) (q : ℕ) (r : ZMod q.succ) :
    residueSum a 0 q r = 0 := by
  classical
  unfold residueSum
  simp

/--
If no element of the window falls in the residue class `r (mod q+1)`,
then the residue sum vanishes.
-/
theorem residueSum_eq_zero_of_forall_ne
    (a : ℕ → ℂ) {N q : ℕ} {r : ZMod q.succ}
    (h : ∀ n ∈ Finset.Icc 1 N, (n : ZMod q.succ) ≠ r) :
    residueSum a N q r = 0 := by
  classical
  unfold residueSum
  -- Show every summand is `0`, then sum them.
  have hzero :
      ∀ n ∈ Finset.Icc 1 N,
        (if ((n : ZMod q.succ) = r) then a n else 0) = 0 := by
    intro n hn
    have hne : (n : ZMod q.succ) ≠ r := h n hn
    by_cases hnr : ((n : ZMod q.succ) = r)
    · exact (hne hnr).elim
    · simp [hnr]
  exact Finset.sum_eq_zero hzero

end Analytic
end Sieve
