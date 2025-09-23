/-
  Sieve/Analytic/BVFirstIneq.lean

  Leaf-level, linter-friendly bricks we will compose into a B ≤ average
  chain (starting with toy parameters). No Stage-3 imports here.

  Contents:
  * `residue_chain_identity` : ∑_r ∑_{n≤N, n%q=r} a(n) = ∑_{n≤N} a(n)  (q>0)
  * `ls_chain_bound`         : large sieve upper bound for residue-filtered squares
-/
import Mathlib
import Sieve.Analytic.ResidueFilterIndicator
import Sieve.Analytic.LargeSieveResidueSquares
import Sieve.Analytic.BVToolboxProgressionsSig

noncomputable section
open Classical

namespace Sieve
namespace Analytic

/-- Residue partition (filtered form), with a stable name for chaining. -/
lemma residue_chain_identity
    (N q : ℕ) (hq : 0 < q) (a : ℕ → ℝ) :
    (∑ r ∈ Finset.range q,
        ∑ n ∈ (Finset.range (N + 1)).filter (fun n => n % q = r), a n)
      = ∑ n ∈ Finset.range (N + 1), a n :=
  residue_partition_filtered N q hq a

/-- Large sieve upper bound in the residue-filtered squares form (stable name). -/
lemma ls_chain_bound
    (TB : BVToolboxProgressionsSig) (q N : ℕ) (a : ℕ → ℝ) :
    (∑ r ∈ Finset.range q,
        (∑ n ∈ (Finset.range (N + 1)).filter (fun n => n % q = r), a n) ^ 2)
      ≤ TB.C_LS * (∑ n ∈ Finset.range (N + 1), (a n) ^ 2) :=
  large_sieve_residue_squares TB q N a

/-- Tiny compile-touch to keep surfaces warm. -/
theorem bvfirst_ineq_compiles (TB : BVToolboxProgressionsSig) : True := by
  let _ := residue_chain_identity 5 3 (by decide) (fun n => (n : ℝ))
  let _ := ls_chain_bound TB 4 6 (fun _ => (1 : ℝ))
  exact True.intro

end Analytic
end Sieve
