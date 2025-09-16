import Mathlib
import MaynardTao.Scenarios
import MaynardTao.Bridging

/-!
MaynardTao/BridgingDemo.lean
----------------------------
Small smoke tests showing how to use the bridging lemmas with the trivial spec.
-/

namespace MaynardTao
namespace BridgingDemo

open Bridging

/-- On the trivial spec, `S_{≥ r} ≤ S₀`. -/
theorem S_atLeast_le_S0_trivial (N : ℕ) (c : ℚ) (hc : 0 < c) (r : ℕ) :
  PrimeCounts.S_atLeast
      (W := (Scenarios.trivialSpec N c hc).W) N
      (Scenarios.trivialSpec N c hc).P.H r
    ≤ Sums.S0 (W := (Scenarios.trivialSpec N c hc).W) N := by
  simpa using
    Bridging.S_atLeast_le_S0
      (W := (Scenarios.trivialSpec N c hc).W)
      N
      (H := (Scenarios.trivialSpec N c hc).P.H)
      r

/-- If numerics give `S_{≥ r} ≥ θ·S₀` for the trivial spec, then
    `S' ≥ (r·θ)·S₀`. This shows how to apply `criterion_from_theta`. -/
theorem trivial_criterion_from_theta
    (N : ℕ) (c : ℚ) (hc : 0 < c) (r : ℕ) (θ : ℚ)
    (hθ :
      PrimeCounts.S_atLeast
        (W := (Scenarios.trivialSpec N c hc).W) N
        (Scenarios.trivialSpec N c hc).P.H r
      ≥ θ * Sums.S0 (W := (Scenarios.trivialSpec N c hc).W) N) :
    (Scenarios.trivialSpec N c hc).Sprime
      ≥ (r : ℚ) * θ * (Scenarios.trivialSpec N c hc).S0 := by
  simpa using
    Bridging.criterion_from_theta
      (s := Scenarios.trivialSpec N c hc) r θ hθ

end BridgingDemo
end MaynardTao
