/-
  Sieve/Stage2Pigeonhole.lean
  Existence of a "heavy" point: some n in the support attains at least the average weight.
-/
import Mathlib
import Sieve.MaynardWeights
import Sieve.MTMoments
import Sieve.ConstWeight
import Sieve.ConstWeightAverage
import Sieve.Pipeline
import Sieve.PipelineSimp

noncomputable section
open Classical

namespace Sieve.Stage2

/-- On any nonempty finite set, some point has value ≥ the average. -/
lemma exists_ge_avg_on_support
    (s : Finset ℤ) (f : ℤ → ℝ) (hpos : 0 < s.card) :
    ∃ n ∈ s, f n ≥ (∑ x ∈ s, f x) / (s.card : ℝ) := by
  classical
  -- pick a maximizer of f on s
  obtain ⟨n, hn, hmax⟩ := s.exists_max_image f (Finset.card_pos.mp hpos)
  -- sum ≤ card * max
  have sum_le : ∑ x ∈ s, f x ≤ (s.card : ℝ) * f n := by
    have : ∑ x ∈ s, f x ≤ ∑ _x ∈ s, f n :=
      Finset.sum_le_sum (fun x hx => hmax x hx)
    simpa [Finset.sum_const, nsmul_eq_mul, mul_comm] using this
  -- divide by card > 0
  have hcpos : 0 < (s.card : ℝ) := by exact_mod_cast hpos
  have hcz : (s.card : ℝ) ≠ 0 := ne_of_gt hcpos
  have := mul_le_mul_of_nonneg_right sum_le (le_of_lt (inv_pos.mpr hcpos))
  -- (∑ f)/card ≤ max = f n
  have : (∑ x ∈ s, f x) / (s.card : ℝ) ≤ f n := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, hcz] using this
  exact ⟨n, hn, this⟩

/-- For any `Weight`, some support point has weight ≥ the average over the support. -/
lemma exists_heavy_ge_average
    (W : Sieve.MaynardWeights.Weight)
    (hpos : 0 < W.support.card) :
    ∃ n ∈ W.support,
      W.w n ≥ (∑ x ∈ W.support, W.w x) / (W.support.card : ℝ) := by
  simpa using exists_ge_avg_on_support W.support W.w hpos

/-- Stage-1 version: some support point has weight ≥ the Stage-1 hit average. -/
lemma exists_heavy_ge_stage1_avg
    (cfg : Sieve.Pipeline.Config)
    (W   : Sieve.MaynardWeights.Weight)
    (hpos : 0 < W.support.card) :
    ∃ n ∈ W.support,
      W.w n ≥ (Sieve.Pipeline.stage1 cfg W).hits.firstMomentLower
                / (W.support.card : ℝ) := by
  simpa [div_eq_mul_inv] using
    exists_heavy_ge_average W hpos

/-- Tiny demo: for a constant weight on a nonempty window, some point reaches at least `c`. -/
example (M : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    let supp := Finset.Icc (-(M : ℤ)) (M : ℤ)
    let W := Sieve.ConstWeight.const supp c hc
    0 < W.support.card →
    ∃ n ∈ W.support, W.w n ≥ c := by
  intro supp W hpos
  -- pick n with weight ≥ average
  obtain ⟨n, hn, h⟩ := exists_heavy_ge_average W hpos
  -- compute the average exactly for a constant weight
  have hpos_supp : 0 < supp.card := by
    simpa [W, Sieve.ConstWeight.const] using hpos
  have avgSum :
      (∑ x ∈ W.support, W.w x) / (W.support.card : ℝ) = c := by
    -- use the exact average lemma for constant weights
    simpa [Sieve.MTMoments.firstMoment, W, Sieve.ConstWeight.const]
      using Sieve.ConstWeight.avg_first_const supp c hc hpos_supp
  -- conclude
  exact ⟨n, hn, by simpa [avgSum] using h⟩

end Sieve.Stage2
