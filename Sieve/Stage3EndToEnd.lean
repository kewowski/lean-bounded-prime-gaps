/-
  Sieve/Stage3EndToEnd.lean
  End-to-end wrappers turning an analytic average lower bound into existence of a hit.
-/
import Mathlib
import Sieve.Stage3Report     -- for heavySet_nonempty_of_avg_ge
import Sieve.AnalyticBridge   -- for AvgWindowHitLB and bridge lemmas

noncomputable section
open Classical BigOperators

namespace Sieve
namespace Stage3

/-- End-to-end (given nonempty heavy set):
If the analytic lower bound at `(W,τ,H,HS)` is ≥ 1, then some heavy point’s window contains a hit. -/
theorem exists_hit_of_AI_ge_one
    (AI : Sieve.Analytic.AvgWindowHitLB)
    (W  : Sieve.MaynardWeights.Weight) (τ : ℝ)
    (H  : Finset ℤ) (HS : Sieve.Stage3.HitSystem)
    (hne : (Sieve.MTCore.heavySet W τ).Nonempty)
    (h1  : 1 ≤ AI.lower W τ H HS hne) :
    ∃ n ∈ Sieve.MTCore.heavySet W τ, ∃ h ∈ H, HS.isHit (n + h) :=
  Sieve.Analytic.exists_heavy_hit_of_lb_ge_one AI W τ H HS hne h1

/-- End-to-end (derive nonempty heavy set from `τ ≤ average`):
If `0 < |support|`, `τ ≤ average`, and the analytic lower bound is ≥ 1,
then some heavy point’s window contains a hit. -/
theorem exists_hit_of_AI_ge_one_from_avg
    (AI : Sieve.Analytic.AvgWindowHitLB)
    (W  : Sieve.MaynardWeights.Weight) (τ : ℝ)
    (H  : Finset ℤ) (HS : Sieve.Stage3.HitSystem)
    (hpos   : 0 < W.support.card)
    (hτleavg : τ ≤ (∑ m ∈ W.support, W.w m) / (W.support.card : ℝ))
    (h1    : 1 ≤ AI.lower W τ H HS
                (Sieve.Stage3.heavySet_nonempty_of_avg_ge (W := W) (τ := τ) hpos hτleavg)) :
    ∃ n ∈ Sieve.MTCore.heavySet W τ, ∃ h ∈ H, HS.isHit (n + h) := by
  classical
  -- derive nonemptiness from the average condition
  have hne : (Sieve.MTCore.heavySet W τ).Nonempty :=
    Sieve.Stage3.heavySet_nonempty_of_avg_ge (W := W) (τ := τ) hpos hτleavg
  -- apply the bridge
  exact Sieve.Analytic.exists_heavy_hit_of_lb_ge_one AI W τ H HS hne h1

end Stage3
end Sieve
namespace Sieve
namespace Stage3

/-- End-to-end (derive nonempty heavy set from `τ ≤ average`, integer threshold):
If `0 < |support|`, `τ ≤ average`, and the analytic lower bound is ≥ `k : ℕ`,
then some heavy point’s window contains at least `k` hits. -/
theorem exists_atLeast_k_hits_of_AI_ge_k_from_avg
    (AI : Sieve.Analytic.AvgWindowHitLB)
    (W  : Sieve.MaynardWeights.Weight) (τ : ℝ)
    (H  : Finset ℤ) (HS : Sieve.Stage3.HitSystem)
    (hpos   : 0 < W.support.card)
    (hτleavg : τ ≤ (∑ m ∈ W.support, W.w m) / (W.support.card : ℝ))
    (k : ℕ)
    (hk    : (k : ℝ) ≤ AI.lower W τ H HS
                (Sieve.Stage3.heavySet_nonempty_of_avg_ge (W := W) (τ := τ) hpos hτleavg)) :
    ∃ n ∈ Sieve.MTCore.heavySet W τ,
      k ≤ (H.filter (fun h => HS.isHit (n + h))).card := by
  classical
  -- derive nonemptiness from the average condition
  have hne : (Sieve.MTCore.heavySet W τ).Nonempty :=
    Sieve.Stage3.heavySet_nonempty_of_avg_ge (W := W) (τ := τ) hpos hτleavg
  -- apply the integer-threshold bridge
  exact
    Sieve.Analytic.exists_heavy_with_atLeast_k_hits_of_lb_ge_k
      (AI := AI) (W := W) (τ := τ) (H := H) (HS := HS) hne k hk

end Stage3
end Sieve
