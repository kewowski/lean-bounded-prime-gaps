/-
  Sieve/Analytic/L1NMonotonicity.lean
  Monotonic-in-`N` *trivial bound* for `residueL1`.

  We do **not** claim `residueL1 a N q` itself is monotone in `N`.
  Instead, we show the standard trivial upper bound grows monotonically
  with `N`, which is often what we need in estimates.
-/
import Mathlib
import Sieve.Analytic.ResidueSumBasics
import Sieve.Analytic.DataMassBasics
import Sieve.Analytic.ResidueL1TrivialBounds
import Sieve.Analytic.L1Monotonicity

noncomputable section
open Classical BigOperators

namespace Sieve
namespace Analytic

/--
Trivial bound monotone in `N`:
for `N ≤ M`,
  `residueL1 a N q ≤ (q+1) * ∑_{n=1}^M ‖a n‖`.
-/
theorem residueL1_trivial_bound_mono_in_N
    (a : ℕ → ℂ) {N M q : ℕ} (hNM : N ≤ M) :
    residueL1 a N q
      ≤ ((q.succ : ℕ) : ℝ) * (∑ n ∈ Finset.Icc 1 M, ‖a n‖) := by
  classical
  have h0 : 0 ≤ ((q.succ : ℕ) : ℝ) := by exact_mod_cast Nat.zero_le (q.succ)
  have hbound := residueL1_le_qsucc_sumNorm_trivial (a := a) (N := N) (q := q)
  have hmono := sum_norm_Icc_monotone_in_N (a := a) (hNM := hNM)
  calc
    residueL1 a N q
        ≤ ((q.succ : ℕ) : ℝ) * (∑ n ∈ Finset.Icc 1 N, ‖a n‖) := hbound
    _   ≤ ((q.succ : ℕ) : ℝ) * (∑ n ∈ Finset.Icc 1 M, ‖a n‖) :=
          mul_le_mul_of_nonneg_left hmono h0

end Analytic
end Sieve
