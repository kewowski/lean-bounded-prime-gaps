/-
  Sieve/Stage3PrimesEndToEnd.lean
  End-to-end wrappers specialized to "hit = primality".
-/
import Mathlib
import Sieve.MTCore
import Sieve.Stage3EndToEnd

noncomputable section
open Classical BigOperators

namespace Sieve
namespace Stage3

/-- Primality as a predicate on integers. -/
def isPrimeZ (n : ℤ) : Prop := Nat.Prime n.natAbs

/-- A `HitSystem` that counts primes. The `cfg` field is carried but unused here. -/
def primeHS (cfg : Sieve.MTCore.TupleConfig) : HitSystem :=
  { cfg := cfg, isHit := isPrimeZ }

/-- End-to-end (derive heavy-set nonempty from `τ ≤ average`, prime hits):
If `0 < |support|`, `τ ≤ average`, and the analytic lower bound is ≥ 1,
then there exists a heavy point whose window contains a prime. -/
theorem exists_prime_in_window_of_AI_ge_one_from_avg
    (AI : Sieve.Analytic.AvgWindowHitLB)
    (W  : Sieve.MaynardWeights.Weight) (τ : ℝ)
    (H  : Finset ℤ) (cfg : Sieve.MTCore.TupleConfig)
    (hpos   : 0 < W.support.card)
    (hτleavg : τ ≤ (∑ m ∈ W.support, W.w m) / (W.support.card : ℝ))
    (h1    : 1 ≤ AI.lower W τ H (primeHS cfg)
                (Sieve.Stage3.heavySet_nonempty_of_avg_ge (W := W) (τ := τ) hpos hτleavg)) :
    ∃ n ∈ Sieve.MTCore.heavySet W τ, ∃ h ∈ H, isPrimeZ (n + h) := by
  classical
  -- delegate to the generic end-to-end wrapper with HS := primeHS cfg
  simpa [primeHS] using
    Sieve.Stage3.exists_hit_of_AI_ge_one_from_avg
      (AI := AI) (W := W) (τ := τ) (H := H) (HS := primeHS cfg)
      (hpos := hpos) (hτleavg := hτleavg) (h1 := h1)

end Stage3
end Sieve
namespace Sieve
namespace Stage3

/-- End-to-end (derive heavy-set nonempty from `τ ≤ average`, integer threshold, prime hits):
If `0 < |support|`, `τ ≤ average`, and the analytic lower bound is ≥ `k : ℕ`,
then there exists a heavy point whose window contains **at least `k` primes**. -/
theorem exists_atLeast_k_primes_in_window_of_AI_ge_k_from_avg
    (AI : Sieve.Analytic.AvgWindowHitLB)
    (W  : Sieve.MaynardWeights.Weight) (τ : ℝ)
    (H  : Finset ℤ) (cfg : Sieve.MTCore.TupleConfig)
    (hpos   : 0 < W.support.card)
    (hτleavg : τ ≤ (∑ m ∈ W.support, W.w m) / (W.support.card : ℝ))
    (k : ℕ)
    (hk    : (k : ℝ) ≤ AI.lower W τ H (primeHS cfg)
                (Sieve.Stage3.heavySet_nonempty_of_avg_ge (W := W) (τ := τ) hpos hτleavg)) :
    ∃ n ∈ Sieve.MTCore.heavySet W τ,
      k ≤ (H.filter (fun h => isPrimeZ (n + h))).card := by
  classical
  -- specialize the generic integer-threshold wrapper with HS := primeHS cfg
  simpa [primeHS] using
    Sieve.Stage3.exists_atLeast_k_hits_of_AI_ge_k_from_avg
      (AI := AI) (W := W) (τ := τ) (H := H) (HS := primeHS cfg)
      (hpos := hpos) (hτleavg := hτleavg) (k := k) (hk := hk)

end Stage3
end Sieve
namespace Sieve
namespace Stage3

/-- Twin-specific wrapper (prime hits):
If `0 < |support|`, `τ ≤ average`, and the analytic lower bound (with prime façade)
is ≥ 1, then there exists a heavy point whose window `{0,2}` contains a prime. -/
theorem exists_prime_in_twin_window_of_AI_ge_one_from_avg
    (AI : Sieve.Analytic.AvgWindowHitLB)
    (W  : Sieve.MaynardWeights.Weight) (τ : ℝ)
    (cfg : Sieve.MTCore.TupleConfig)
    (hpos   : 0 < W.support.card)
    (hτleavg : τ ≤ (∑ m ∈ W.support, W.w m) / (W.support.card : ℝ))
    (h1    : 1 ≤ AI.lower W τ (([0, 2] : List ℤ).toFinset) (primeHS cfg)
                (Sieve.Stage3.heavySet_nonempty_of_avg_ge (W := W) (τ := τ) hpos hτleavg)) :
    ∃ n ∈ Sieve.MTCore.heavySet W τ, ∃ h ∈ (([0, 2] : List ℤ).toFinset), isPrimeZ (n + h) := by
  classical
  -- Just specialize the general prime-window lemma with H = {0,2}.
  simpa using
    Sieve.Stage3.exists_prime_in_window_of_AI_ge_one_from_avg
      (AI := AI) (W := W) (τ := τ)
      (H := (([0, 2] : List ℤ).toFinset)) (cfg := cfg)
      (hpos := hpos) (hτleavg := hτleavg) (h1 := h1)

end Stage3
end Sieve
namespace Sieve
namespace Stage3

/-- Twin-specific wrapper (prime hits, integer threshold):
If `0 < |support|`, `τ ≤ average`, and the analytic lower bound (with prime façade)
is ≥ `k : ℕ`, then there exists a heavy point whose window `{0,2}` contains **at least `k` primes**. -/
theorem exists_atLeast_k_primes_in_twin_window_of_AI_ge_k_from_avg
    (AI : Sieve.Analytic.AvgWindowHitLB)
    (W  : Sieve.MaynardWeights.Weight) (τ : ℝ)
    (cfg : Sieve.MTCore.TupleConfig)
    (hpos   : 0 < W.support.card)
    (hτleavg : τ ≤ (∑ m ∈ W.support, W.w m) / (W.support.card : ℝ))
    (k : ℕ)
    (hk    : (k : ℝ) ≤ AI.lower W τ (([0, 2] : List ℤ).toFinset) (primeHS cfg)
                (Sieve.Stage3.heavySet_nonempty_of_avg_ge (W := W) (τ := τ) hpos hτleavg)) :
    ∃ n ∈ Sieve.MTCore.heavySet W τ,
      k ≤ ((([0, 2] : List ℤ).toFinset).filter (fun h => isPrimeZ (n + h))).card := by
  classical
  -- specialize the general integer-threshold prime-window lemma with H = {0,2}.
  simpa using
    Sieve.Stage3.exists_atLeast_k_primes_in_window_of_AI_ge_k_from_avg
      (AI := AI) (W := W) (τ := τ)
      (H := (([0, 2] : List ℤ).toFinset)) (cfg := cfg)
      (hpos := hpos) (hτleavg := hτleavg) (k := k) (hk := hk)

end Stage3
end Sieve
