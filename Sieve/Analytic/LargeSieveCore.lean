/-
  Sieve/Analytic/LargeSieveCore.lean
  Leaf analytic toolbox for BV/EH-style inputs to Stage-3.

  This file carries typed statement signatures only (no proofs),
  keeping the repo green while downstream analytic work fills them.
-/
import Mathlib

noncomputable section
open Classical BigOperators

namespace Sieve
namespace Analytic

/--
Sum of a sequence `a : ℕ → ℂ` along the residue class `r (mod q+1)` up to `N`.
We use `Finset.Icc 1 N` to avoid the `0` edge case and `(n : ZMod q.succ)` to
test membership in the residue class without peeking at `r`.
-/
def residueSum (a : ℕ → ℂ) (N q : ℕ) (r : ZMod q.succ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, if ((n : ZMod q.succ) = r) then a n else 0

/--
Bare-bones analytic toolbox for Bombieri–Vinogradov / Elliott–Halberstam style
inputs to the Stage-3 pipeline. Fields are *assumptions* (typed statements)
to be discharged later by analytic modules; keeping them here prevents import
cycles and heavy dependencies in core Stage-2/3 code.
-/
structure BVToolbox where
  /-- Absolute constant in the large sieve inequality. Take `C_ls ≥ 1`. -/
  C_ls : ℝ
  C_ls_pos : 1 ≤ C_ls

  /--
  Large sieve over residue progressions (character-free form).

  For any sequence `a : ℕ → ℂ`, the total L² mass of residue-class sums
  over all moduli `0 ≤ q ≤ Q` and all residues `r (mod q+1)` is bounded by
  `C_ls * (N + Q^2)` times the L² mass of `a` up to `N`.

  We index `q` by `Finset.range (Q+1)` so `q = 0` contributes a benign term
  (mod 1), and `ZMod q.succ` avoids division-by-zero pathologies.
  -/
  largeSieve_residueProgressions :
    ∀ {N Q : ℕ} (a : ℕ → ℂ),
      1 ≤ N → 1 ≤ Q →
      (∑ q ∈ Finset.range (Q + 1),
         ∑ r : ZMod q.succ,
           ‖residueSum a N q r‖^2)
      ≤ C_ls * (N + Q^2) * (∑ n ∈ Finset.Icc 1 N, ‖a n‖^2)

  /--
  Dyadic-window large sieve over residue progressions.

  The same inequality restricted to an interval of moduli `Q₁ ≤ q ≤ Q₂`,
  bounded with the natural `Q₂` scale. This is the form typically used
  after dyadic decomposition in BV/EH arguments.
  -/
  largeSieve_residueProgressions_dyadic :
    ∀ {N Q₁ Q₂ : ℕ} (a : ℕ → ℂ),
      1 ≤ N → Q₁ ≤ Q₂ → 1 ≤ Q₂ →
      (∑ q ∈ Finset.Icc Q₁ Q₂,
         ∑ r : ZMod q.succ,
           ‖residueSum a N q r‖^2)
      ≤ C_ls * (N + Q₂^2) * (∑ n ∈ Finset.Icc 1 N, ‖a n‖^2)

  /--
  Weighted large sieve over residue progressions.

  As the unweighted form, but with a nonnegative weight `w q ≤ 1` on each modulus.
  This is handy when one smooths a dyadic partition or discounts small moduli.
  -/
  largeSieve_residueProgressions_weighted :
    ∀ {N Q : ℕ} (a : ℕ → ℂ) (w : ℕ → ℝ),
      (∀ q, 0 ≤ w q ∧ w q ≤ 1) →
      1 ≤ N → 1 ≤ Q →
      (∑ q ∈ Finset.range (Q + 1),
          w q * (∑ r : ZMod q.succ, ‖residueSum a N q r‖^2))
      ≤ C_ls * (N + Q^2) * (∑ n ∈ Finset.Icc 1 N, ‖a n‖^2)

  /--
  Discrete partial summation (summation by parts), typed identity (no proof here).

  This is the standard Abel/partial summation formula on `ℕ` with
  unit-step increments encoded by `A n - A (n - 1)`. It is stated over `ℝ`
  for downstream bounding; an ℂ-version can be added similarly if needed.
  -/
  partialSummation_identity :
    ∀ {N : ℕ} (A Δ : ℕ → ℝ),
      A 0 = 0 →
      (∑ n ∈ Finset.Icc 1 N, (A n - A (n - 1)) * Δ n)
      = A N * Δ N
        - ∑ n ∈ Finset.Icc 1 (N - 1), A n * (Δ (n + 1) - Δ n)

  /--
  A convenient Abel-type *inequality* under monotonicity assumptions.

  If the "weights" `Δ` are nonincreasing on `[1, N]` and the increments
  `A n - A (n-1)` are nonnegative (so `A` is nondecreasing with `A 0 = 0`),
  then the partial summation gives the bound

    ∑_{n=1}^N (A n - A (n-1)) * Δ n ≤ Δ 1 * A N.

  This is the form most directly consumed in BV-style arguments when one
  controls a decreasing weight and an accumulated sum `A`.
  -/
  partialSummation_decreasingBound :
    ∀ {N : ℕ} (A Δ : ℕ → ℝ),
      A 0 = 0 →
      (∀ n, 1 ≤ n → 0 ≤ A n - A (n - 1)) →
      (∀ n, 1 ≤ n ∧ n < N → Δ (n + 1) ≤ Δ n) →
      0 ≤ Δ 1 →
      (∑ n ∈ Finset.Icc 1 N, (A n - A (n - 1)) * Δ n)
        ≤ Δ 1 * A N

  /--
  Orthogonality of residue indicators (character-free combinatorial identity).

  For `q ≥ 0` and any `n, m`, the indicator vectors of residues are orthonormal:
  summing over residues `r : ZMod (q+1)`, the overlap of the indicators of
  `n ≡ r` and `m ≡ r` is `1` iff `n ≡ m (mod q+1)`, else `0`.
  -/
  orthogonality_residueIndicators :
    ∀ {q n m : ℕ},
      (∑ r : ZMod q.succ,
          (if ((n : ZMod q.succ) = r) then (1 : ℝ) else 0)
        * (if ((m : ZMod q.succ) = r) then (1 : ℝ) else 0))
      = (if ((n : ZMod q.succ) = (m : ZMod q.succ)) then (1 : ℝ) else 0)

  /--
  Cauchy–Schwarz packaging across the `(q,r)` residue index.

  An `ℓ¹`–`ℓ²` bridge: the sum of absolute values of the residue sums is bounded by
  the square root of the index size times the square root of the `ℓ²`-mass. This
  is often paired with `largeSieve_residueProgressions` to control `ℓ¹`.
  -/
  CS_residueL1_from_L2 :
    ∀ {N Q : ℕ} (a : ℕ → ℂ),
      1 ≤ N → 1 ≤ Q →
      (∑ q ∈ Finset.range (Q + 1),
         ∑ r : ZMod q.succ, ‖residueSum a N q r‖)
      ≤ Real.sqrt
          (∑ q ∈ Finset.range (Q + 1), ((q.succ : ℕ) : ℝ))
        * Real.sqrt
          (∑ q ∈ Finset.range (Q + 1),
             ∑ r : ZMod q.succ, ‖residueSum a N q r‖^2)

  /--
  Per-modulus Cauchy–Schwarz: control the L¹ over residues at a fixed modulus `q`
  by the square root of the residue count `q+1` times the L² over residues.

    ∑_{r mod q+1} ‖S(q,r)‖ ≤ √(q+1) * √( ∑_{r} ‖S(q,r)‖² ),

  where `S(q,r) = residueSum a N q r`.
  -/
  CS_residueL1_from_L2_perModulus :
    ∀ {N q : ℕ} (a : ℕ → ℂ),
      1 ≤ N →
      (∑ r : ZMod q.succ, ‖residueSum a N q r‖)
      ≤ Real.sqrt (((q.succ : ℕ) : ℝ))
        * Real.sqrt (∑ r : ZMod q.succ, ‖residueSum a N q r‖^2)

end Analytic
end Sieve

