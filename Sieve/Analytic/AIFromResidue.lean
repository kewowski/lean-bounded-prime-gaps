/-
  Sieve/Analytic/AIFromResidue.lean

  Constructor: a pointwise window-density lower bound over the heavy set
  ⇒ an average lower bound ⇒ a Stage-3 analytic input `AvgWindowHitLB`.
-/
import Mathlib
import Sieve.AnalyticInputs
import Sieve.Analytic.AIConstructors

noncomputable section
open Classical

namespace Sieve
namespace Analytic

/-- Minimal spec: a constant `δ` and a *pointwise* lower bound over the heavy set. -/
structure ResidueLBSpec where
  δ : ℝ
  per_point :
    ∀ (W : Sieve.MaynardWeights.Weight) (τ : ℝ)
      (H : Finset ℤ) (HS : Sieve.Stage3.HitSystem)
      (_hne : (Sieve.MTCore.heavySet W τ).Nonempty),
      ∀ n ∈ Sieve.MTCore.heavySet W τ,
        δ * (H.card : ℝ)
          ≤ Sieve.Stage3.windowSum H (Sieve.Stage3.hitIndicator HS) n

/-- If `c ≤ f n` for every heavy point `n`, then `c ≤ avgOver heavy f`. -/
lemma avg_ge_of_pointwise_heavy
    (W : Sieve.MaynardWeights.Weight) (τ : ℝ)
    (H : Finset ℤ) (HS : Sieve.Stage3.HitSystem)
    (hne : (Sieve.MTCore.heavySet W τ).Nonempty)
    (c : ℝ)
    (hpt :
      ∀ n ∈ Sieve.MTCore.heavySet W τ,
        c ≤ Sieve.Stage3.windowSum H (Sieve.Stage3.hitIndicator HS) n)
    : c ≤
        Sieve.Stage3.avgOver (Sieve.MTCore.heavySet W τ)
          (Sieve.Stage3.windowSum H (Sieve.Stage3.hitIndicator HS)) := by
  classical
  set A := Sieve.MTCore.heavySet W τ
  -- Sum the pointwise inequalities over A.
  have hsum_le :
      (∑ n ∈ A, c)
        ≤ ∑ n ∈ A, Sieve.Stage3.windowSum H (Sieve.Stage3.hitIndicator HS) n := by
    exact Finset.sum_le_sum (by intro n hn; exact hpt n hn)
  -- The constant sum is |A| * c.
  have hsum_left : (∑ _n ∈ A, c) = (A.card : ℝ) * c := by
    simp [Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hpos : 0 < (A.card : ℝ) := by
    exact_mod_cast (Finset.card_pos.mpr hne)
  have hne0 : (A.card : ℝ) ≠ 0 := ne_of_gt hpos
  -- Divide both sides by |A| > 0 (after rewriting LHS to |A|*c).
  have hdiv' :
      ((A.card : ℝ) * c) / (A.card : ℝ)
        ≤ (∑ n ∈ A, Sieve.Stage3.windowSum H (Sieve.Stage3.hitIndicator HS) n)
            / (A.card : ℝ) := by
    have h' : (A.card : ℝ) * c
              ≤ ∑ n ∈ A, Sieve.Stage3.windowSum H (Sieve.Stage3.hitIndicator HS) n := by
      simpa [hsum_left] using hsum_le
    exact div_le_div_of_nonneg_right h' (le_of_lt hpos)
  -- LHS simplifies to c; RHS is the average.
  have : c ≤
      (∑ n ∈ A, Sieve.Stage3.windowSum H (Sieve.Stage3.hitIndicator HS) n) / (A.card : ℝ) := by
    -- `((|A|*c)/|A|) = c` via `simp` with `div_eq_mul_inv` and `hne0`.
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, hne0] using hdiv'
  -- Rewrite RHS into the avgOver definition.
  simpa [Sieve.Stage3.avgOver, div_eq_mul_inv] using this

/-- Package a residue-driven (pointwise) density LB into `AvgWindowHitLB`. -/
@[inline] def AI_fromResidue (S : ResidueLBSpec) : AvgWindowHitLB :=
  AnalyticInputs.ofLower
    (fun _W _τ H _HS _hne => S.δ * (H.card : ℝ))
    (fun W τ H HS hne =>
      avg_ge_of_pointwise_heavy W τ H HS hne (c := S.δ * (H.card : ℝ))
        (S.per_point W τ H HS hne))

/-- Smoke: the constructor compiles and yields the right type. -/
theorem ai_from_residue_compiles (S : ResidueLBSpec) : True := by
  let _AI : AvgWindowHitLB := AI_fromResidue S
  exact True.intro

end Analytic
end Sieve
