import Mathlib
import Sieve.Analytic.ToyWeightDemo

noncomputable section
open Classical

namespace Sieve.Tests

-- Heavy set is nonempty for τ = 1/2 (since 1/2 ≤ 1).
example : (Sieve.MTCore.heavySet Sieve.Analytic.W0 ((1 : ℝ) / 2)).Nonempty :=
  Sieve.Analytic.heavySet_W0_nonempty_of_tau_le_one (by norm_num)

-- Monotonicity: if τ₁ ≤ τ₂ then |heavy(τ₂)| ≤ |heavy(τ₁)|.
-- Concretely, τ₁=0 ≤ τ₂=1 ⇒ card at 1 ≤ card at 0.
example :
  (Sieve.MTCore.heavySet Sieve.Analytic.W0 1).card
    ≤ (Sieve.MTCore.heavySet Sieve.Analytic.W0 0).card :=
by
  simpa using Sieve.Analytic.heavy_card_mono_for_W0 (τ₁ := 0) (τ₂ := 1) (by norm_num)

end Sieve.Tests
