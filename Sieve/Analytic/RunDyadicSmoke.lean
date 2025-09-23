/-
  Sieve/Analytic/RunDyadicSmoke.lean
  Tiny smoke test exercising the dyadic large-sieve field from `BVToolbox`.
  Keeps the repo green by re-exposing the typed inequality with a `simpa`.
-/
import Mathlib
import Sieve.Analytic.LargeSieveCore

noncomputable section
open Classical BigOperators

namespace Sieve
namespace Analytic

variable (T : BVToolbox) {N Q₁ Q₂ : ℕ} (a : ℕ → ℂ)

/-- Smoke wrapper for the dyadic large-sieve inequality over `q ∈ [Q₁, Q₂]`. -/
theorem demo_largeSieve_dyadic
    (hN : 1 ≤ N) (hQ : Q₁ ≤ Q₂) (hQ2 : 1 ≤ Q₂) :
    (∑ q ∈ Finset.Icc Q₁ Q₂,
       ∑ r : ZMod q.succ,
         ‖residueSum a N q r‖^2)
      ≤ T.C_ls * (N + Q₂^2) * (∑ n ∈ Finset.Icc 1 N, ‖a n‖^2) :=
by
  simpa using
    T.largeSieve_residueProgressions_dyadic a hN hQ hQ2

end Analytic
end Sieve

