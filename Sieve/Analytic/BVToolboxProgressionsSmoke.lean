/-
  Sieve/Analytic/BVToolboxProgressionsSmoke.lean
  UTF-8 (no BOM), ASCII-only.

  Purpose
  -------
  Minimal smoke that *references* each field of `BVToolboxProgressionsSig`.
  If any signature changes, this file will fail to build — early warning.
  No analysis; just type usage to keep us honest.

  House rules:
  • Leaf imports only (the signatures file).
  • Tiny proofs, no heavy tactics.
-/
import Mathlib
import Sieve.Analytic.BVToolboxProgressionsSig

noncomputable section
open scoped BigOperators
open Finset

namespace Sieve
namespace Analytic

/-- Touch the large-sieve inequality field (shape only). -/
theorem bvtoolbox_progressions_smoke_LS
    (TB : BVToolboxProgressionsSig) : True := by
  classical
  -- Use a specific (q,N,a) so the type elaborates:
  let q := 5
  let N := 7
  let a : ℕ → ℝ := fun n => (n : ℝ)
  -- Obtain the inequality (ignore its content, only the type matters).
  have _hLS := TB.large_sieve_progressions q N a
  exact True.intro

/-- Touch the orthogonality identity field (shape only). -/
theorem bvtoolbox_progressions_smoke_orth
    (TB : BVToolboxProgressionsSig) : True := by
  classical
  have _hOrth := TB.orthogonality_indicator 6 2
  exact True.intro

/-- Touch the discrete partial summation field (shape only). -/
theorem bvtoolbox_progressions_smoke_dps
    (TB : BVToolboxProgressionsSig) : True := by
  classical
  let N := 4
  let a : ℕ → ℝ := fun n => (n : ℝ)
  let A : ℕ → ℝ := fun n => ∑ k ∈ Finset.range (n+1), a k
  have _hDPS := TB.discrete_partial_summation N a A
  exact True.intro

end Analytic
end Sieve
