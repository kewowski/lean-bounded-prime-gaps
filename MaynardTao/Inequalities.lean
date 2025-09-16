import Mathlib
import MaynardTao.ShiftPrimes
import MaynardTao.PrimeCounts
import MaynardTao.Sums
import MaynardTao.WeightsAPI
import MaynardTao.BoundedGaps

/-!
MaynardTao/Inequalities.lean
----------------------------
A proof-free specification layer for the key Maynard–Tao inequality:

  S_prime(W,N,H) ≥ (r : ℚ) * S_atLeast(W,N,H,r)

Plus lightweight upper bounds to sandwich the sums.
-/

namespace MaynardTao
namespace Inequalities

open scoped BigOperators

variable {P : WeightParams}

/-- For a fixed `n`, the total of prime-indicators over shifts in `H`. -/
noncomputable def sumPrimeIndicators (H : Finset ℤ) (n : ℕ) : ℚ := by
  classical
  exact ∑ h ∈ H, MaynardTao.indicator (primePred h n)

/-- Nonnegativity of `sumPrimeIndicators`. -/
lemma sumPrimeIndicators_nonneg (H : Finset ℤ) (n : ℕ) :
    0 ≤ sumPrimeIndicators H n := by
  classical
  unfold sumPrimeIndicators
  refine Finset.sum_nonneg ?_
  intro h hh
  exact MaynardTao.indicator_nonneg (primePred h n)

/-- Identify the sum of indicators with the (casted) count of prime shifts. -/
lemma sumPrimeIndicators_eq_count_cast (H : Finset ℤ) (n : ℕ) :
    sumPrimeIndicators H n
      = (PrimeCounts.count H n : ℚ) := by
  classical
  have hswap :
      ∑ h ∈ H, (if primePred h n then (1 : ℚ) else 0)
        = ∑ h ∈ H.filter (fun h => primePred h n), (1 : ℚ) := by
    simpa using
      (Finset.sum_filter (s := H)
        (p := fun h => primePred h n)
        (f := fun _ => (1 : ℚ))).symm
  unfold sumPrimeIndicators
  simp [PrimeCounts.count, MaynardTao.indicator, hswap, Finset.sum_const, nsmul_eq_mul]

/-- Swap the order of summation in `S_prime` and factor the weight. -/
lemma S_prime_as_sum_n (W : SieveWeight P) (N : ℕ) (H : Finset ℤ) :
    ShiftPrimes.S_prime (W := W) N H
      = ∑ n ∈ (W.restrict N).support,
          (W.restrict N).w n * sumPrimeIndicators H n := by
  classical
  unfold ShiftPrimes.S_prime
  unfold Sums.S_of
  have hcomm :
      ∑ h ∈ H, ∑ n ∈ (W.restrict N).support,
        (W.restrict N).w n * MaynardTao.indicator (primePred h n)
      =
      ∑ n ∈ (W.restrict N).support, ∑ h ∈ H,
        (W.restrict N).w n * MaynardTao.indicator (primePred h n) := by
    simpa using
      (Finset.sum_comm
        (s := H) (t := (W.restrict N).support)
        (f := fun h n => (W.restrict N).w n * MaynardTao.indicator (primePred h n)))
  have hfact :
      ∑ n ∈ (W.restrict N).support, ∑ h ∈ H,
        (W.restrict N).w n * MaynardTao.indicator (primePred h n)
      =
      ∑ n ∈ (W.restrict N).support,
        (W.restrict N).w n * ∑ h ∈ H, MaynardTao.indicator (primePred h n) := by
    refine Finset.sum_congr rfl ?_
    intro n hn
    simpa using
      (Finset.mul_sum (a := (W.restrict N).w n) (s := H)
        (f := fun h => MaynardTao.indicator (primePred h n))).symm
  simpa [sumPrimeIndicators] using hcomm.trans hfact

/-- The global inequality target for a fixed `W, N, H, r`. -/
noncomputable def RCrit (W : SieveWeight P) (N : ℕ) (H : Finset ℤ) (r : ℕ) : Prop :=
  ShiftPrimes.S_prime (W := W) N H ≥ (r : ℚ) * PrimeCounts.S_atLeast (W := W) N H r

/-- Same inequality expressed inside the `BoundedGaps.Spec` bundle. -/
noncomputable def RCritSpec (s : BoundedGaps.Spec) (r : ℕ) : Prop :=
  ShiftPrimes.S_prime (W := s.W) s.N s.P.H ≥ (r : ℚ) * PrimeCounts.S_atLeast (W := s.W) s.N s.P.H r

/-- Baseline: the inequality holds for `r = 0`. -/
lemma RCrit_zero (W : SieveWeight P) (N : ℕ) (H : Finset ℤ) :
    RCrit (W := W) N H 0 := by
  classical
  unfold RCrit
  simpa [zero_mul] using ShiftPrimes.S_prime_nonneg (W := W) N H

/-- Baseline (Spec-version): the inequality holds for `r = 0`. -/
lemma RCritSpec_zero (s : BoundedGaps.Spec) :
    RCritSpec s 0 := by
  classical
  unfold RCritSpec
  simpa [zero_mul] using ShiftPrimes.S_prime_nonneg (W := s.W) s.N s.P.H

/-- Pointwise (per-`n`) lower bound using the classical indicator. -/
lemma sumPrimeIndicators_ge_r_cIndicator (H : Finset ℤ) (r n : ℕ) :
    sumPrimeIndicators H n ≥ (r : ℚ) * MaynardTao.cIndicator (PrimeCounts.atLeast H r n) := by
  classical
  set m : ℕ := PrimeCounts.count H n
  have hm : sumPrimeIndicators H n = (m : ℚ) := by
    simpa [m] using sumPrimeIndicators_eq_count_cast H n
  by_cases hr : r ≤ m
  · have hrq : (r : ℚ) ≤ (m : ℚ) := by exact_mod_cast hr
    have hind : MaynardTao.cIndicator (r ≤ m) = 1 := by
      simp [MaynardTao.cIndicator, MaynardTao.indicator, hr]
    have hgoal : (r : ℚ) * MaynardTao.cIndicator (r ≤ m) ≤ (m : ℚ) := by
      simpa [hind, mul_one] using hrq
    simpa [hm] using hgoal
  · have h0q : 0 ≤ (m : ℚ) := by exact_mod_cast (Nat.zero_le m)
    have hind : MaynardTao.cIndicator (r ≤ m) = 0 := by
      simp [MaynardTao.cIndicator, MaynardTao.indicator, hr]
    have hgoal : (r : ℚ) * MaynardTao.cIndicator (r ≤ m) ≤ (m : ℚ) := by
      simpa [hind, mul_zero] using h0q
    simpa [hm] using hgoal

/-- Aggregate the pointwise bound to obtain the global inequality. -/
lemma RCrit_all (W : SieveWeight P) (N : ℕ) (H : Finset ℤ) (r : ℕ) :
    RCrit (W := W) N H r := by
  classical
  unfold RCrit
  set S := (W.restrict N).support
  set wR := (W.restrict N).w
  have hswap := S_prime_as_sum_n (W := W) N H
  have hstep :
      ∑ n ∈ S, wR n * sumPrimeIndicators H n
        ≥ ∑ n ∈ S, wR n * ((r : ℚ) * MaynardTao.cIndicator (PrimeCounts.atLeast H r n)) := by
    refine (ge_iff_le).mpr ?_
    refine Finset.sum_le_sum ?_
    intro n hn
    have base :=
      (sumPrimeIndicators_ge_r_cIndicator (H := H) (r := r) (n := n))
    have base_le : (r : ℚ) * MaynardTao.cIndicator (PrimeCounts.atLeast H r n)
                    ≤ sumPrimeIndicators H n := by
      simpa using base
    have hw : 0 ≤ wR n := (W.restrict N).nonneg n
    have := mul_le_mul_of_nonneg_left base_le hw
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  have hrhs :
      ∑ n ∈ S, wR n * ((r : ℚ) * MaynardTao.cIndicator (PrimeCounts.atLeast H r n))
        = (r : ℚ) * PrimeCounts.S_atLeast (W := W) N H r := by
    calc
      ∑ n ∈ S, wR n * ((r : ℚ) * MaynardTao.cIndicator (PrimeCounts.atLeast H r n))
          = ∑ n ∈ S, (r : ℚ) * (wR n * MaynardTao.cIndicator (PrimeCounts.atLeast H r n)) := by
                refine Finset.sum_congr rfl ?_; intro n hn; ring
      _ = (r : ℚ) * ∑ n ∈ S, (wR n * MaynardTao.cIndicator (PrimeCounts.atLeast H r n)) := by
                simpa using
                  (Finset.mul_sum (a := (r : ℚ)) (s := S)
                    (f := fun n => wR n * MaynardTao.cIndicator (PrimeCounts.atLeast H r n))).symm
      _ = (r : ℚ) * PrimeCounts.S_atLeast (W := W) N H r := by
                unfold PrimeCounts.S_atLeast Sums.S_of
                simp [MaynardTao.cIndicator, MaynardTao.indicator, S, wR]
  have hL : ShiftPrimes.S_prime (W := W) N H
              = ∑ n ∈ S, wR n * sumPrimeIndicators H n := by
    simpa [S, wR] using hswap
  have hR : (r : ℚ) * PrimeCounts.S_atLeast (W := W) N H r
              = ∑ n ∈ S, wR n * ((r : ℚ) * MaynardTao.cIndicator (PrimeCounts.atLeast H r n)) := by
    simpa [S, wR] using hrhs.symm
  simpa [hL, hR, ge_iff_le] using hstep

/-- Spec-version of the global inequality. -/
lemma RCritSpec_all (s : BoundedGaps.Spec) (r : ℕ) :
    RCritSpec s r := by
  classical
  unfold RCritSpec
  simpa using RCrit_all (W := s.W) s.N s.P.H r

/-- Upper bound: for each `n`, the sum of prime indicators is at most `H.card`. -/
lemma sumPrimeIndicators_le_card (H : Finset ℤ) (n : ℕ) :
    sumPrimeIndicators H n ≤ (H.card : ℚ) := by
  classical
  unfold sumPrimeIndicators
  have hpoint : ∀ h ∈ H, MaynardTao.indicator (primePred h n) ≤ (1 : ℚ) := by
    intro h hh
    by_cases b : primePred h n
    · simp [MaynardTao.indicator, b]
    · simp [MaynardTao.indicator, b]
  have hsum_le :
      ∑ h ∈ H, MaynardTao.indicator (primePred h n)
        ≤ ∑ h ∈ H, (1 : ℚ) :=
    Finset.sum_le_sum hpoint
  -- Sum of ones over H is |H| (as a rational).
  simpa [Finset.sum_const, nsmul_eq_mul, mul_one]
    using hsum_le

/-- Global upper bound: `S' ≤ |H| * S0`. -/
lemma S_prime_le_cardH_S0 (W : SieveWeight P) (N : ℕ) (H : Finset ℤ) :
    ShiftPrimes.S_prime (W := W) N H ≤ (H.card : ℚ) * Sums.S0 (W := W) N := by
  classical
  -- rewrite S' as sum over n
  have hrepr := S_prime_as_sum_n (W := W) N H
  -- bound inner term by |H|
  have hbound :
      ∑ n ∈ (W.restrict N).support,
          (W.restrict N).w n * sumPrimeIndicators H n
        ≤
      ∑ n ∈ (W.restrict N).support,
          (W.restrict N).w n * (H.card : ℚ) := by
    refine Finset.sum_le_sum ?_
    intro n hn
    have : sumPrimeIndicators H n ≤ (H.card : ℚ) := sumPrimeIndicators_le_card H n
    have hw : 0 ≤ (W.restrict N).w n := (W.restrict N).nonneg n
    exact mul_le_mul_of_nonneg_left this hw
  -- compute the right-hand sum as (H.card) * S0
  have hsum :
      ∑ n ∈ (W.restrict N).support, (W.restrict N).w n * (H.card : ℚ)
        = (H.card : ℚ) * Sums.S0 (W := W) N := by
    unfold Sums.S0 SieveWeight.total
    -- pull the scalar out
    simpa [mul_comm, mul_left_comm, mul_assoc]
      using
        (Finset.mul_sum (a := (H.card : ℚ))
          (s := (W.restrict N).support)
          (f := fun n => (W.restrict N).w n)).symm
  -- chain equalities/inequality explicitly
  calc
    ShiftPrimes.S_prime (W := W) N H
        = ∑ n ∈ (W.restrict N).support, (W.restrict N).w n * sumPrimeIndicators H n := by
            simpa using hrepr
    _   ≤ ∑ n ∈ (W.restrict N).support, (W.restrict N).w n * (H.card : ℚ) := hbound
    _   = (H.card : ℚ) * Sums.S0 (W := W) N := hsum

end Inequalities
end MaynardTao
