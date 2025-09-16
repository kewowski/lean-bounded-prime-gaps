import Mathlib
import MaynardTao.Inequalities
import MaynardTao.PrimeCounts
import MaynardTao.Sums
import MaynardTao.ShiftPrimes

/-!
MaynardTao/Monotonicity.lean
----------------------------
Monotonicity with respect to enlarging the shift set `H`.

* `sumPrimeIndicators_mono_H` : per-`n` sum is monotone in `H`
* `S_prime_mono_H`            : global prime sum is monotone in `H`
* `S_atLeast_mono_H`          : `S_{≥ r}` is monotone in `H`
-/

namespace MaynardTao
namespace Monotonicity

open scoped BigOperators
variable {P : WeightParams}

/-- If `H₁ ⊆ H₂` then for each `n` we have
    `∑_{h∈H₁} 1_{prime(n+h)} ≤ ∑_{h∈H₂} 1_{prime(n+h)}`. -/
lemma sumPrimeIndicators_mono_H
    {H₁ H₂ : Finset ℤ} (hsub : H₁ ⊆ H₂) (n : ℕ) :
    Inequalities.sumPrimeIndicators H₁ n
      ≤ Inequalities.sumPrimeIndicators H₂ n := by
  classical
  -- subset on filtered sets
  have hsubset :
      H₁.filter (fun h => primePred h n) ⊆ H₂.filter (fun h => primePred h n) := by
    intro x hx
    rcases Finset.mem_filter.mp hx with ⟨hxH1, hxP⟩
    exact Finset.mem_filter.mpr ⟨hsub hxH1, hxP⟩
  -- cardinalities are monotone under subset
  have hcard :
      (H₁.filter (fun h => primePred h n)).card
        ≤ (H₂.filter (fun h => primePred h n)).card :=
    Finset.card_mono hsubset
  -- turn it into a ℚ inequality via counts
  have hcount : PrimeCounts.count H₁ n ≤ PrimeCounts.count H₂ n := by
    simpa [PrimeCounts.count] using hcard
  have hq : (PrimeCounts.count H₁ n : ℚ) ≤ (PrimeCounts.count H₂ n : ℚ) := by
    exact_mod_cast hcount
  -- rewrite both sides with `sumPrimeIndicators = (count : ℚ)`
  simpa [Inequalities.sumPrimeIndicators_eq_count_cast] using hq

/-- If `H₁ ⊆ H₂` then the global prime sum is monotone:
    `S'(W,N,H₁) ≤ S'(W,N,H₂)`. -/
lemma S_prime_mono_H (W : SieveWeight P) (N : ℕ)
    {H₁ H₂ : Finset ℤ} (hsub : H₁ ⊆ H₂) :
    ShiftPrimes.S_prime (W := W) N H₁ ≤ ShiftPrimes.S_prime (W := W) N H₂ := by
  classical
  -- Put both sides in the "sum over n times sumPrimeIndicators" form.
  have h1 := Inequalities.S_prime_as_sum_n (W := W) N H₁
  have h2 := Inequalities.S_prime_as_sum_n (W := W) N H₂
  -- Compare termwise using monotonicity of `sumPrimeIndicators`.
  have hsum :
      ∑ n ∈ (W.restrict N).support,
          (W.restrict N).w n * Inequalities.sumPrimeIndicators H₁ n
      ≤
      ∑ n ∈ (W.restrict N).support,
          (W.restrict N).w n * Inequalities.sumPrimeIndicators H₂ n := by
    refine Finset.sum_le_sum ?_
    intro n hn
    have hmono := sumPrimeIndicators_mono_H (H₁ := H₁) (H₂ := H₂) hsub n
    have hw : 0 ≤ (W.restrict N).w n := (W.restrict N).nonneg n
    exact mul_le_mul_of_nonneg_left hmono hw
  -- Assemble.
  simpa [h1, h2] using hsum

/-- If `H₁ ⊆ H₂` then `S_{≥ r}` is monotone:
    `S_atLeast(W,N,H₁,r) ≤ S_atLeast(W,N,H₂,r)`. -/
lemma S_atLeast_mono_H (W : SieveWeight P) (N : ℕ)
    {H₁ H₂ : Finset ℤ} (hsub : H₁ ⊆ H₂) (r : ℕ) :
    PrimeCounts.S_atLeast (W := W) N H₁ r ≤
    PrimeCounts.S_atLeast (W := W) N H₂ r := by
  classical
  unfold PrimeCounts.S_atLeast Sums.S_of
  refine Finset.sum_le_sum ?_
  intro n hn
  have hw : 0 ≤ (W.restrict N).w n := (W.restrict N).nonneg n
  -- At-least event is monotone in `H`.
  have hsubset :
      H₁.filter (fun h => primePred h n) ⊆ H₂.filter (fun h => primePred h n) := by
    intro x hx
    rcases Finset.mem_filter.mp hx with ⟨hxH1, hxP⟩
    exact Finset.mem_filter.mpr ⟨hsub hxH1, hxP⟩
  have hcard :
      (H₁.filter (fun h => primePred h n)).card
        ≤ (H₂.filter (fun h => primePred h n)).card :=
    Finset.card_mono hsubset
  have hcount :
      PrimeCounts.count H₁ n ≤ PrimeCounts.count H₂ n := by
    simpa [PrimeCounts.count] using hcard
  have hatLeast_mono :
      MaynardTao.indicator (PrimeCounts.atLeast H₁ r n)
        ≤ MaynardTao.indicator (PrimeCounts.atLeast H₂ r n) := by
    by_cases hr1 : r ≤ PrimeCounts.count H₁ n
    · have hr2 : r ≤ PrimeCounts.count H₂ n := le_trans hr1 hcount
      simp [PrimeCounts.atLeast, MaynardTao.indicator, hr1, hr2]
    · -- left indicator is 0; right is ≥ 0
      have : MaynardTao.indicator (PrimeCounts.atLeast H₁ r n) = 0 := by
        simp [PrimeCounts.atLeast, MaynardTao.indicator, hr1]
      have hnonneg : 0 ≤ MaynardTao.indicator (PrimeCounts.atLeast H₂ r n) :=
        MaynardTao.indicator_nonneg _
      simpa [this]
  exact mul_le_mul_of_nonneg_left hatLeast_mono hw

end Monotonicity
end MaynardTao
