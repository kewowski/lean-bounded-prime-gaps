import Mathlib
import MaynardTao.WeightsAPI
import MaynardTao.Sums
import MaynardTao.PrimeCounts
import MaynardTao.Inequalities
import MaynardTao.BoundedGaps

/-!
MaynardTao/Bridging.lean
------------------------
Simple inequalities that bridge the global Maynard–Tao target with the classic
`criterion` in `BoundedGaps.Spec`.

* `S_atLeast_le_S0`           : S_{≥r} ≤ S0
* `S_atLeast_mono_r`          : r₂ ≥ r₁ ⇒ S_{≥r₂} ≤ S_{≥r₁}
* `criterion_from_theta`      : if S_{≥r} ≥ θ·S0 then S' ≥ (r·θ)·S0
-/

namespace MaynardTao
namespace Bridging

open scoped BigOperators
variable {P : WeightParams}

/-- Trivial upper bound: `S_atLeast ≤ S0` (since indicators ≤ 1). -/
lemma S_atLeast_le_S0 (W : SieveWeight P) (N : ℕ) (H : Finset ℤ) (r : ℕ) :
    PrimeCounts.S_atLeast (W := W) N H r ≤ Sums.S0 (W := W) N := by
  classical
  -- Expand both sides as sums over `(W.restrict N).support`.
  unfold PrimeCounts.S_atLeast Sums.S_of Sums.S0 SieveWeight.total
  -- Compare termwise using `indicator ≤ 1`.
  refine Finset.sum_le_sum ?_
  intro n hn
  have hw : 0 ≤ (W.restrict N).w n := (W.restrict N).nonneg n
  have hind : MaynardTao.indicator (PrimeCounts.atLeast H r n) ≤ (1 : ℚ) := by
    by_cases h : PrimeCounts.atLeast H r n
    · simp [MaynardTao.indicator, h]
    · simp [MaynardTao.indicator, h]
  -- w n * indicator ≤ w n * 1
  simpa using (mul_le_mul_of_nonneg_left hind hw)

/-- Monotonicity in `r`: if `r₂ ≥ r₁`, then `S_{≥ r₂} ≤ S_{≥ r₁}`. -/
lemma S_atLeast_mono_r (W : SieveWeight P) (N : ℕ) (H : Finset ℤ)
    {r₁ r₂ : ℕ} (h : r₂ ≥ r₁) :
    PrimeCounts.S_atLeast (W := W) N H r₂ ≤ PrimeCounts.S_atLeast (W := W) N H r₁ := by
  classical
  unfold PrimeCounts.S_atLeast Sums.S_of
  refine Finset.sum_le_sum ?_
  intro n hn
  have hw : 0 ≤ (W.restrict N).w n := (W.restrict N).nonneg n
  -- indicators are antitone in r: 1_{r₂ ≤ count} ≤ 1_{r₁ ≤ count} when r₂ ≥ r₁
  have hind :
      MaynardTao.indicator (PrimeCounts.atLeast H r₂ n)
        ≤ MaynardTao.indicator (PrimeCounts.atLeast H r₁ n) := by
    by_cases hr2le : r₂ ≤ PrimeCounts.count H n
    · have hr1le : r₁ ≤ PrimeCounts.count H n := le_trans h hr2le
      -- both sides = 1
      simp [PrimeCounts.atLeast, MaynardTao.indicator, hr2le, hr1le]
    · -- left = 0; right ≥ 0
      have : MaynardTao.indicator (PrimeCounts.atLeast H r₂ n) = 0 := by
        simp [PrimeCounts.atLeast, MaynardTao.indicator, hr2le]
      have hnonneg : 0 ≤ MaynardTao.indicator (PrimeCounts.atLeast H r₁ n) :=
        MaynardTao.indicator_nonneg _
      simpa [this]
  exact mul_le_mul_of_nonneg_left hind hw

/-- If `S_{≥ r} ≥ θ·S0`, then combining with `RCritSpec_all` yields
`S' ≥ (r·θ)·S0`. -/
lemma criterion_from_theta (s : BoundedGaps.Spec) (r : ℕ) (θ : ℚ)
    (hθ : PrimeCounts.S_atLeast (W := s.W) s.N s.P.H r ≥ θ * Sums.S0 (W := s.W) s.N) :
    s.Sprime ≥ (r : ℚ) * θ * s.S0 := by
  classical
  -- From `RCritSpec_all`: S' ≥ r * S_{≥ r}
  have base_ge : s.Sprime ≥ (r : ℚ) * PrimeCounts.S_atLeast (W := s.W) s.N s.P.H r :=
    Inequalities.RCritSpec_all (s := s) r
  -- Flip to `≤` for chaining.
  have baseLE : (r : ℚ) * PrimeCounts.S_atLeast (W := s.W) s.N s.P.H r ≤ s.Sprime := by
    simpa [ge_iff_le] using base_ge
  -- Use the assumption, flipped to `≤`, then multiply by `(r:ℚ) ≥ 0`.
  have hθLE : θ * Sums.S0 (W := s.W) s.N ≤
              PrimeCounts.S_atLeast (W := s.W) s.N s.P.H r := by
    simpa [ge_iff_le] using hθ
  have hr0 : 0 ≤ (r : ℚ) := by exact_mod_cast (Nat.zero_le r)
  have stepLE :
      (r : ℚ) * (θ * Sums.S0 (W := s.W) s.N)
        ≤ (r : ℚ) * PrimeCounts.S_atLeast (W := s.W) s.N s.P.H r :=
    mul_le_mul_of_nonneg_left hθLE hr0
  -- Chain: (r·θ)·S0 ≤ r*S_{≥r} ≤ S'
  have boundLE : (r : ℚ) * (θ * s.S0) ≤ s.Sprime := by
    -- rewrite s.S0 to Sums.S0 inside
    simpa using le_trans stepLE baseLE
  -- Present as ≥ with nicer association.
  simpa [ge_iff_le, mul_left_comm, mul_assoc] using boundLE

end Bridging
end MaynardTao
