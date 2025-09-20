/-
  Sieve/Stage3PrimeFacade.lean
  A neutral "prime-hit" façade for Stage 3:
  - wrap a tuple config + an abstract hit predicate,
  - indicator-based window sums,
  - extract a hit from an average ≥ 1 on the heavy set.
-/
import Mathlib
import Sieve.MTCore
import Sieve.Stage3Window

noncomputable section
open Classical BigOperators

namespace Sieve
namespace Stage3

/-- Abstract hit system: a tuple configuration plus a boolean "hit" predicate. -/
structure HitSystem where
  cfg   : Sieve.MTCore.TupleConfig
  isHit : ℤ → Prop

/-- Indicator for hits (0/1 as `ℝ`). -/
def hitIndicator (HS : HitSystem) : ℤ → ℝ :=
  fun n => if HS.isHit n then (1 : ℝ) else 0

/-- A convenient alias: window hit *count* as a real (sum of 0/1s). -/
def windowHitCount (H : Finset ℤ) (HS : HitSystem) (n : ℤ) : ℝ :=
  Sieve.Stage3.windowSum H (hitIndicator HS) n

/-- If the sum of 0/1 indicators over `H` is ≥ 1, there is a hit in that window. -/
theorem exists_hit_of_windowIndicator_sum_ge_one
    (H : Finset ℤ) (P : ℤ → Prop) (n : ℤ)
    (h1 : 1 ≤ ∑ h ∈ H, (if P (n + h) then (1 : ℝ) else 0)) :
    ∃ h ∈ H, P (n + h) := by
  classical
  by_contra hnone
  -- `hnone : ¬ ∃ h ∈ H, P (n + h)` ⇒ all indicators are 0 ⇒ sum = 0
  have hnone' : ¬ ∃ h, h ∈ H ∧ P (n + h) := by
    simpa [exists_prop] using hnone
  have hforall : ∀ h ∈ H, ¬ P (n + h) := by
    intro h hh; exact fun ph => hnone' ⟨h, ⟨hh, ph⟩⟩
  have hsum0 :
      (∑ h ∈ H, (if P (n + h) then (1 : ℝ) else 0)) = 0 := by
    have :
        (∑ h ∈ H, (if P (n + h) then (1 : ℝ) else 0))
          = ∑ h ∈ H, (0 : ℝ) := by
      refine Finset.sum_congr rfl ?_
      intro h hh; have := hforall h hh; simp [this]
    simpa using this
  -- 1 ≤ 0 is impossible
  have hnot : ¬ (1 : ℝ) ≤ 0 := not_le.mpr (zero_lt_one)
  exact hnot (by simpa [hsum0] using h1)

/-- **Extraction lemma (façade):**
If the average window hit count over the `τ`-heavy set is ≥ 1,
then some heavy point has a hit in its window. -/
theorem exists_heavy_with_hit_from_avg_ge_one
    (W : Sieve.MaynardWeights.Weight) (τ : ℝ)
    (H : Finset ℤ) (HS : HitSystem)
    (hne : (Sieve.MTCore.heavySet W τ).Nonempty)
    (hAvg : 1 ≤ Sieve.Stage3.avgOver (Sieve.MTCore.heavySet W τ)
              (Sieve.Stage3.windowSum H (hitIndicator HS))) :
    ∃ n ∈ Sieve.MTCore.heavySet W τ, ∃ h ∈ H, HS.isHit (n + h) := by
  classical
  -- pick n in the heavy set where windowSum ≥ the average
  obtain ⟨n, hnA, havg_le⟩ :=
    Sieve.Stage3.exists_heavy_with_window_ge_avg
      (W := W) (τ := τ) (H := H) (f := hitIndicator HS) hne
  -- 1 ≤ avg ≤ windowSum ⇒ 1 ≤ windowSum
  have hge1 :
      1 ≤ Sieve.Stage3.windowSum H (hitIndicator HS) n :=
    le_trans hAvg havg_le
  -- windowSum is the indicator sum; ≥ 1 ⇒ some hit exists
  have : ∃ h ∈ H, HS.isHit (n + h) := by
    simpa [Sieve.Stage3.windowSum, hitIndicator]
      using exists_hit_of_windowIndicator_sum_ge_one
        (H := H) (P := HS.isHit) (n := n) hge1
  rcases this with ⟨h, hhH, hhit⟩
  exact ⟨n, hnA, h, hhH, hhit⟩

end Stage3
end Sieve
