/-
  Sieve/Stage3PrimeCountsNat.lean
  Integer-threshold extraction: avg ≥ k (Nat) ⇒ ∃ heavy point with ≥ k hits.
-/
import Mathlib
import Sieve.MTCore
import Sieve.Stage3Window
import Sieve.Stage3PrimeFacade
import Sieve.Stage3PrimeCounts     -- real-threshold version
import Sieve.Stage3HitCard         -- windowHitCount_eq_card_filter

noncomputable section
open Classical BigOperators

namespace Sieve
namespace Stage3

/-- If the average window **hit count** over the τ-heavy set is ≥ `k : ℕ`,
then there exists a heavy point whose window has at least `k` hits (cardinality form). -/
theorem exists_heavy_with_atLeast_k_hits
    (W : Sieve.MaynardWeights.Weight) (τ : ℝ)
    (H : Finset ℤ) (HS : HitSystem)
    (hne : (Sieve.MTCore.heavySet W τ).Nonempty)
    (k : ℕ)
    (hAvg :
      (k : ℝ) ≤ Sieve.Stage3.avgOver (Sieve.MTCore.heavySet W τ)
                (Sieve.Stage3.windowSum H (Sieve.Stage3.hitIndicator HS))) :
    ∃ n ∈ Sieve.MTCore.heavySet W τ,
      k ≤ (H.filter (fun h => HS.isHit (n + h))).card := by
  classical
  -- real-threshold witness with t = k
  obtain ⟨n, hnA, hreal⟩ :=
    Sieve.Stage3.exists_heavy_with_hitcount_ge
      (W := W) (τ := τ) (H := H) (HS := HS) hne (t := (k : ℝ)) hAvg
  -- rewrite to windowHitCount first, then to a cardinality
  have hcount :
      (k : ℝ) ≤ Sieve.Stage3.windowHitCount H HS n := by
    simpa [Sieve.Stage3.windowHitCount,
           Sieve.Stage3.windowSum,
           Sieve.Stage3.hitIndicator] using hreal
  have hcard_real :
      (k : ℝ) ≤ ((H.filter (fun h => HS.isHit (n + h))).card : ℝ) := by
    simpa [Sieve.Stage3.windowHitCount_eq_card_filter] using hcount
  -- cast down to Nat
  have hNat : k ≤ (H.filter (fun h => HS.isHit (n + h))).card := by
    exact_mod_cast hcard_real
  exact ⟨n, hnA, hNat⟩

end Stage3
end Sieve
