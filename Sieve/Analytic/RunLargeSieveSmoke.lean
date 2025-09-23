/-
  Sieve/Analytic/RunLargeSieveSmoke.lean
  Tiny smoke test that exercises the typed large sieve field from BVToolbox.
  Keeps the repo green (no proofs beyond a `simpa`) and imports only the leaf toolbox.
-/
import Mathlib
import Sieve.Analytic.LargeSieveCore

noncomputable section
open Classical BigOperators

namespace Sieve
namespace Analytic

variable (T : BVToolbox) {N Q : ℕ} (a : ℕ → ℂ)

/-- Thin wrapper that re-exposes the toolbox bound for convenient use in demos/tests. -/
theorem demo_largeSieve_bound (hN : 1 ≤ N) (hQ : 1 ≤ Q) :
    (∑ q ∈ Finset.range (Q + 1),
       ∑ r : ZMod q.succ,
         ‖residueSum a N q r‖^2)
  ≤ T.C_ls * (N + Q^2) * (∑ n ∈ Finset.Icc 1 N, ‖a n‖^2) :=
by
  simpa using T.largeSieve_residueProgressions a hN hQ

end Analytic
end Sieve

