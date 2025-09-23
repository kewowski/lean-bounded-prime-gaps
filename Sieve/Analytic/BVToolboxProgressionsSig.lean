/-
  Sieve/Analytic/BVToolboxProgressionsSig.lean
  UTF-8 (no BOM), ASCII-only.

  Purpose
  -------
  Signatures-only record for the analytic toolbox pieces we will discharge
  with Bombieri–Vinogradov / Elliott–Halberstam later. No proofs here.
  This file is a leaf and safe to depend on.

  Fields (shapes only):
  • large_sieve_progressions : constant-carrying inequality over residue classes
  • orthogonality_indicator  : indicator orthogonality over modulo q
  • discrete_partial_summation : discrete partial summation identity (shape)

  House rules:
  • Leaf module (no import hubs).
  • No proofs; just types. Keep everything Prop/∀… so nothing heavy elaborates.
  • Use modern finset sum notation `∑ x ∈ s, f x`.
-/
import Mathlib

noncomputable section
open scoped BigOperators
open Finset

namespace Sieve
namespace Analytic

/--
Signatures-only toolbox for progression sums and related analytic identities.
No proofs; these are the exact shapes downstream analysis will provide.
-/
structure BVToolboxProgressionsSig where
  /-- A large-sieve style inequality over residue classes modulo `q`.
      For any `a : ℕ → ℝ` supported on `[0..N]`, the sum of squared residue-window sums
      is bounded by a constant `C_LS` times the global L². -/
  C_LS : ℝ
  large_sieve_progressions :
    ∀ (q N : ℕ) (a : ℕ → ℝ),
      (∑ r ∈ Finset.range q,
          (∑ n ∈ (Finset.range (N + 1)).filter (fun n => n % q = r), a n) ^ 2)
        ≤ C_LS * (∑ n ∈ Finset.range (N + 1), (a n) ^ 2)

  /-- Orthogonality of residue-class indicators over `ℕ` modulo `q`. -/
  orthogonality_indicator :
    ∀ (q r : ℕ),
      (∑ n ∈ Finset.range q, (if n % q = r then (1 : ℝ) else 0))
        = (if r ∈ Finset.range q then (1 : ℝ) else 0)

  /-- Discrete partial summation (shape only). For a sequence `a` with partial sums `A`,
      this gives the standard Abel/partial-summation identity on `[0..N]`. We state the
      identity over `ℝ`-valued sequences with natural indices. -/
  discrete_partial_summation :
    ∀ (N : ℕ) (a A : ℕ → ℝ),
      -- Shape: sum_{n=0}^N a(n) = A(N) - A(0) + sum_{n=0}^{N-1} (A(n) - A(n+1))
      -- We phrase an equality that downstream lemmas can rewrite to the usual form.
      (∑ n ∈ Finset.range (N + 1), a n)
        = A N - A 0 + (∑ n ∈ Finset.range N, (A n - A (n + 1)))

end Analytic
end Sieve
