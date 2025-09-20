import Mathlib
import MaynardTao.BoundedGaps
import MaynardTao.PrimeCounts
import MaynardTao.Sums
import MaynardTao.SpecGlue
import MaynardTao.Inequalities

/-!
MaynardTao/NumericLower.lean
----------------------------
A minimal numerical lower-bound interface.

* `lower_of_nonpos` : if `θ ≤ 0`, then `θ * S0 ≤ S_{≥ r}` (since both sides are ≥ 0 up to the factor).
* `criterion_from_RCrit_all_and_nonpos` : end-to-end demo: `RCritSpec_all` + `θ ≤ 0` ⇒ `criterion` for
  `s.withLambda ((r:ℚ) * θ)`.
-/

namespace MaynardTao
namespace NumericLower

open MaynardTao BoundedGaps
open scoped BigOperators

/-- Trivial lower bound: if `θ ≤ 0`, then `θ * S0 ≤ S_{≥ r}`. -/
lemma lower_of_nonpos (s : BoundedGaps.Spec) (r : ℕ) {θ : ℚ}
    (hθ : θ ≤ 0) :
    θ * Sums.S0 (W := s.W) s.N ≤
      PrimeCounts.S_atLeast (W := s.W) s.N s.P.H r := by
  classical
  -- both sides are nonnegative except for the factor θ
  have hS0 : 0 ≤ Sums.S0 (W := s.W) s.N := BoundedGaps.Spec.S0_nonneg s
  have hR  : 0 ≤ PrimeCounts.S_atLeast (W := s.W) s.N s.P.H r :=
    PrimeCounts.S_atLeast_nonneg (W := s.W) s.N s.P.H r
  -- θ ≤ 0 and S0 ≥ 0 ⇒ θ * S0 ≤ 0
  have hL : θ * Sums.S0 (W := s.W) s.N ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hθ hS0
  -- chain to the RHS ≥ 0
  exact le_trans hL hR

/-- End-to-end demo: global Maynard–Tao inequality + `θ ≤ 0` gives `criterion`
    for `s.withLambda ((r:ℚ) * θ)`. -/
lemma criterion_from_RCrit_all_and_nonpos
    (s : BoundedGaps.Spec) (r : ℕ) {θ : ℚ}
    (hθ : θ ≤ 0) :
    BoundedGaps.Spec.criterion (s.withLambda ((r : ℚ) * θ)) := by
  classical
  -- RCrit for all r
  have hRCrit : Inequalities.RCritSpec s r :=
    Inequalities.RCritSpec_all s r
  -- trivial lower bound
  have hLow : θ * Sums.S0 (W := s.W) s.N ≤
      PrimeCounts.S_atLeast (W := s.W) s.N s.P.H r :=
    lower_of_nonpos s r hθ
  -- glue to criterion
  exact BoundedGaps.Spec.criterion_withLambda_of_RCrit_and_lower s r θ hRCrit hLow

end NumericLower
end MaynardTao
-- Append to MaynardTao/NumericLower.lean

namespace MaynardTao
namespace NumericLower

open BoundedGaps

/-- If a θ-fraction (by weight) of the support satisfies `atLeast H r`,
then `θ * S0 ≤ S_{≥ r}`. This is just notation-chasing. -/
lemma lower_of_weighted_fraction
    (s : BoundedGaps.Spec) (r : ℕ) {θ : ℚ} 
    (hmass :
      ∑ n ∈ (s.W.restrict s.N).support,
        (s.W.restrict s.N).w n *
          MaynardTao.cIndicator (PrimeCounts.atLeast s.P.H r n)
      ≥
      θ * ∑ n ∈ (s.W.restrict s.N).support, (s.W.restrict s.N).w n) :
    θ * Sums.S0 (W := s.W) s.N ≤
      PrimeCounts.S_atLeast (W := s.W) s.N s.P.H r := by
  classical
  -- Just unfold both sides (`S0`, `S_atLeast`) and reuse `hmass`.
  simpa [Sums.S0, PrimeCounts.S_atLeast] using hmass

/-- End-to-end: if a θ-fraction (by weight) of the support meets `atLeast H r`,
then `criterion` holds for `s.withLambda ((r:ℚ) * θ)`. -/
lemma criterion_from_RCrit_all_and_mass
    (s : BoundedGaps.Spec) (r : ℕ) {θ : ℚ} 
    (hmass :
      ∑ n ∈ (s.W.restrict s.N).support,
        (s.W.restrict s.N).w n *
          MaynardTao.cIndicator (PrimeCounts.atLeast s.P.H r n)
      ≥
      θ * ∑ n ∈ (s.W.restrict s.N).support, (s.W.restrict s.N).w n) :
    BoundedGaps.Spec.criterion (s.withLambda ((r : ℚ) * θ)) := by
  classical
  have hRCrit := Inequalities.RCritSpec_all s r
  have hLower := lower_of_weighted_fraction s r hmass
  exact BoundedGaps.Spec.criterion_withLambda_of_RCrit_and_lower s r θ hRCrit hLower

end NumericLower
end MaynardTao

