/-
  Sieve/Analytic/WeightedResidueL1TrivialBounds.lean
  Trivial L¹ bound for *weighted* residue sums (no large-sieve input).

  Result:
    • `residueL1W_le_qsucc_sum_absw_norm` :
        ∑_{r mod q+1} ‖residueSumW a w N q r‖
          ≤ (q+1) · ∑_{n=1}^N (|w n| · ‖a n‖)
-/
import Mathlib
import Sieve.Analytic.ResidueSumBasics
import Sieve.Analytic.WeightedResidue

noncomputable section
open Classical BigOperators

namespace Sieve
namespace Analytic

/--
Per-modulus weighted L¹ trivial bound via triangle inequality:
  ∑_{r mod q+1} ‖residueSumW a w N q r‖
    ≤ (q+1) * ∑_{n=1}^N (|w n| * ‖a n‖).
-/
theorem residueL1W_le_qsucc_sum_absw_norm
    (a : ℕ → ℂ) (w : ℕ → ℝ) (N q : ℕ) :
    (∑ r : ZMod q.succ, ‖residueSumW a w N q r‖)
      ≤ ((q.succ : ℕ) : ℝ)
          * (∑ n ∈ Finset.Icc 1 N, (|w n| * ‖a n‖)) := by
  classical
  -- For each residue, drop the indicator and bound the summand's norm.
  have hpt :
      ∀ r : ZMod q.succ,
        ‖residueSumW a w N q r‖
          ≤ ∑ n ∈ Finset.Icc 1 N, (|w n| * ‖a n‖) := by
    intro r
    -- Triangle inequality on the inner sum.
    have h₁ :
        ‖∑ n ∈ Finset.Icc 1 N,
            (if ((n : ZMod q.succ) = r) then ((w n : ℂ) * a n) else 0)‖
          ≤ ∑ n ∈ Finset.Icc 1 N,
              ‖if ((n : ZMod q.succ) = r) then ((w n : ℂ) * a n) else 0‖ := by
      exact
        (norm_sum_le (s := Finset.Icc 1 N)
                     (f := fun n => (if ((n : ZMod q.succ) = r) then ((w n : ℂ) * a n) else 0)))
    -- Compare each summand to |w n|‖a n‖.
    have h₂ :
        (∑ n ∈ Finset.Icc 1 N,
            ‖if ((n : ZMod q.succ) = r) then ((w n : ℂ) * a n) else 0‖)
          ≤ (∑ n ∈ Finset.Icc 1 N, (|w n| * ‖a n‖)) := by
      refine Finset.sum_le_sum ?term
      intro n _hn
      by_cases h : ((n : ZMod q.succ) = r)
      · -- Indicator true: summand simplifies to |w n| * ‖a n‖.
        -- `Complex.norm_real` : ‖(x : ℂ)‖ = |x|.
        -- `norm_mul` : ‖z₁*z₂‖ = ‖z₁‖ * ‖z₂‖.
        simp [h, Complex.norm_real, mul_comm]
      · -- Indicator false: LHS is 0 ≤ |w n|‖a n‖.
        have : 0 ≤ |w n| * ‖a n‖ := mul_nonneg (abs_nonneg _) (norm_nonneg _)
        simpa [h] using this
    -- Chain.
    simpa [residueSumW] using (le_trans h₁ h₂)
  -- Sum over all residues and evaluate the constant sum.
  have :
      (∑ r : ZMod q.succ, ‖residueSumW a w N q r‖)
        ≤ (∑ _r : ZMod q.succ,
            (∑ n ∈ Finset.Icc 1 N, (|w n| * ‖a n‖))) :=
    Finset.sum_le_sum (fun r _ => hpt r)
  simpa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end Analytic
end Sieve
