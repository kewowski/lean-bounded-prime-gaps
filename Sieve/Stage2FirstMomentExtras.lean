/-
  Sieve/Stage2FirstMomentExtras.lean
  Empty-set corollary from the first-moment (Markov) bound.
-/
import Mathlib
import Sieve.MaynardWeights
import Sieve.MTMoments
import Sieve.Stage2Thresholds

noncomputable section
open Classical

namespace Sieve
namespace Stage2

/-- If `τ > 0`, `∑ w ≤ |support| * M`, and `( |support| * M / τ ) < 1`,
then the non-strict `τ`-heavy set is empty. -/
theorem heavy_nonstrict_empty_of_firstMoment_lt
    (W : Sieve.MaynardWeights.Weight) {M τ : ℝ}
    (hτpos : 0 < τ)
    (h_first : (∑ n ∈ W.support, W.w n) ≤ (W.support.card : ℝ) * M)
    (hlt : (W.support.card : ℝ) * M / τ < 1) :
    (W.support.filter (fun n => τ ≤ W.w n)).card = 0 := by
  classical
  set s : Finset ℤ := W.support
  set A : Finset ℤ := s.filter (fun n => τ ≤ W.w n)
  have hbound :
      (A.card : ℝ) ≤ (s.card : ℝ) * M / τ :=
    Sieve.Stage2.heavy_count_le_of_firstMoment
      (W := W) (M := M) (τ := τ) hτpos (by simpa [s] using h_first)
  have hlt' : (A.card : ℝ) < 1 := lt_of_le_of_lt hbound (by simpa [s] using hlt)
  by_contra hne
  have : (1 : ℝ) ≤ (A.card : ℝ) := by
    have : 1 ≤ A.card := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hne)
    exact_mod_cast this
  exact (not_le_of_gt hlt') this

end Stage2
end Sieve
