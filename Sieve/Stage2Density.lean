/-
  Sieve/Stage2Density.lean
  Density bound from the first-moment (Markov) inequality.

  If 0 < |support| and τ > 0 and
    ∑_{support} w ≤ |support| * M,
  then
    density({n ∈ support | τ ≤ w n}) ≤ M / τ.
-/
import Mathlib
import Sieve.MaynardWeights
import Sieve.MTMoments
import Sieve.Stage2Thresholds

noncomputable section
open Classical BigOperators

namespace Sieve
namespace Stage2

/-- Heavy-set density bound from the first moment. -/
theorem heavy_density_le_of_firstMoment
    (W : Sieve.MaynardWeights.Weight) {M τ : ℝ}
    (hpos  : 0 < W.support.card)
    (hτpos : 0 < τ)
    (h_first : (∑ n ∈ W.support, W.w n) ≤ (W.support.card : ℝ) * M) :
    ((W.support.filter (fun n => τ ≤ W.w n)).card : ℝ) / (W.support.card : ℝ)
      ≤ M / τ := by
  classical
  set s : Finset ℤ := W.support
  have hscard_pos : 0 < (s.card : ℝ) := by exact_mod_cast hpos
  have hcnt : ((s.filter (fun n => τ ≤ W.w n)).card : ℝ)
                ≤ (s.card : ℝ) * M / τ :=
    Sieve.Stage2.heavy_count_le_of_firstMoment
      (W := W) (M := M) (τ := τ) hτpos (by simpa [s] using h_first)
  -- divide both sides by |s| > 0
  have hdiv :
      ((s.filter (fun n => τ ≤ W.w n)).card : ℝ) / (s.card : ℝ)
        ≤ ((s.card : ℝ) * M / τ) / (s.card : ℝ) :=
    div_le_div_of_nonneg_right hcnt (le_of_lt hscard_pos)
  -- simplify RHS to M/τ
  have rhs_simp :
      ((s.card : ℝ) * M / τ) / (s.card : ℝ) = M / τ := by
    have hscard_ne : (s.card : ℝ) ≠ 0 := ne_of_gt hscard_pos
    calc
      ((s.card : ℝ) * M / τ) / (s.card : ℝ)
          = ((s.card : ℝ) * (M / τ)) / (s.card : ℝ) := by
              simp [mul_div_assoc]
      _ = M / τ := by
              -- ((|s|) * X) / |s| = X, since |s| ≠ 0
              simp [div_eq_mul_inv, hscard_ne, mul_comm, mul_assoc]
  -- conclude
  have hdiv' :
      ((s.filter (fun n => τ ≤ W.w n)).card : ℝ) / (s.card : ℝ)
        ≤ M / τ := by
    simpa [rhs_simp] using hdiv
  simpa [s] using hdiv'

end Stage2
end Sieve

