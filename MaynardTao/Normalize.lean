import Mathlib
import MaynardTao.WeightsAPI
import MaynardTao.WeightOps2

/-!
MaynardTao/Normalize.lean
-------------------------
Normalize a weight to have total mass 1 (when total > 0), reusing `SieveWeight.scale`.

Provides:
* `SieveWeight.total_scale`      : total of a scaled weight
* `SieveWeight.normalize`        : scale by `1 / total`
* `SieveWeight.total_normalize`  : the normalized total equals 1
-/

namespace MaynardTao
namespace SieveWeight

variable {P : WeightParams}

/-- Total mass after scaling by `c`. -/
@[simp] lemma total_scale (W : SieveWeight P) (c : ℚ)
    (hc0 : 0 ≤ c) (hcz : c ≠ 0) :
    (W.scale c hc0 hcz).total = c * W.total := by
  classical
  -- `a * ∑ f = ∑ a * f` (use symmetry to match shapes).
  have h1 :
      ∑ n ∈ W.support, c * W.w n
        = c * ∑ n ∈ W.support, W.w n := by
    simpa using
      (Finset.mul_sum (a := c) (s := W.support) (f := fun n => W.w n)).symm
  simpa [SieveWeight.total, SieveWeight.scale] using h1

/-- Normalize a weight so that its total mass is exactly 1.
Requires `0 < W.total`, ensuring the scale factor is positive and nonzero. -/
def normalize (W : SieveWeight P) (hpos : 0 < W.total) : SieveWeight P :=
  W.scale (1 / W.total)
    (le_of_lt (div_pos (show 0 < (1 : ℚ) from zero_lt_one) hpos))
    (div_ne_zero (by exact one_ne_zero) (ne_of_gt hpos))

/-- The normalized weight has total exactly 1. -/
@[simp] lemma total_normalize (W : SieveWeight P) (hpos : 0 < W.total) :
    (W.normalize hpos).total = 1 := by
  classical
  have hne : W.total ≠ 0 := ne_of_gt hpos
  have hc0 : 0 ≤ 1 / W.total :=
    le_of_lt (div_pos (show 0 < (1 : ℚ) from zero_lt_one) hpos)
  have hcz : 1 / W.total ≠ 0 :=
    div_ne_zero (by exact one_ne_zero) hne
  calc
    (W.normalize hpos).total
        = (W.scale (1 / W.total) hc0 hcz).total := by
            simp [normalize]
    _   = (1 / W.total) * W.total := by
            simp [total_scale]
    _   = 1 := by
            exact (one_div_mul_cancel hne)

end SieveWeight
end MaynardTao
