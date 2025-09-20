/-
  Sieve/Stage3PrimeCounts.lean
  Real-threshold extraction for window hit counts over the heavy set.
-/
import Mathlib
import Sieve.MTCore
import Sieve.Stage3Window
import Sieve.Stage3PrimeFacade

noncomputable section
open Classical BigOperators

namespace Sieve
namespace Stage3

/-- If the average window **hit count** over the τ-heavy set is ≥ `t : ℝ`,
then there exists a heavy point with window-hit count ≥ `t`. -/
theorem exists_heavy_with_hitcount_ge
    (W : Sieve.MaynardWeights.Weight) (τ : ℝ)
    (H : Finset ℤ) (HS : HitSystem)
    (hne : (Sieve.MTCore.heavySet W τ).Nonempty)
    {t : ℝ}
    (hAvg : t ≤ Sieve.Stage3.avgOver (Sieve.MTCore.heavySet W τ)
              (Sieve.Stage3.windowSum H (hitIndicator HS))) :
    ∃ n ∈ Sieve.MTCore.heavySet W τ,
      t ≤ Sieve.Stage3.windowSum H (hitIndicator HS) n := by
  classical
  -- pick n in the heavy set where windowSum ≥ the average
  obtain ⟨n, hnA, havg_le⟩ :=
    Sieve.Stage3.exists_heavy_with_window_ge_avg
      (W := W) (τ := τ) (H := H) (f := hitIndicator HS) hne
  -- t ≤ avg ≤ windowSum ⇒ t ≤ windowSum
  exact ⟨n, hnA, le_trans hAvg havg_le⟩

/-- Special case `t = 1`: matches the façade lemma but keeps a uniform signature. -/
theorem exists_heavy_with_hit_from_avg_ge_one'
    (W : Sieve.MaynardWeights.Weight) (τ : ℝ)
    (H : Finset ℤ) (HS : HitSystem)
    (hne : (Sieve.MTCore.heavySet W τ).Nonempty)
    (hAvg : 1 ≤ Sieve.Stage3.avgOver (Sieve.MTCore.heavySet W τ)
              (Sieve.Stage3.windowSum H (hitIndicator HS))) :
    ∃ n ∈ Sieve.MTCore.heavySet W τ, ∃ h ∈ H, HS.isHit (n + h) := by
  -- re-use the existing façade lemma verbatim
  simpa using
    Sieve.Stage3.exists_heavy_with_hit_from_avg_ge_one
      (W := W) (τ := τ) (H := H) (HS := HS) hne hAvg

end Stage3
end Sieve
