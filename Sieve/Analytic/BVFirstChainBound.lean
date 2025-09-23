/-
  Sieve/Analytic/BVFirstChainBound.lean

  Leaf-level bricks for the DPS → residues → LS chain.
  We define a named residue-block sum and expose two stable lemmas:

    • `sum_residueBlocks_eq_total` :
        ∑_{r<q} (∑_{n≤N, n%q=r} a n) = ∑_{n≤N} a n        (q>0)
      (residue partition identity, filtered form)

    • `ls_on_residueBlocks` :
        ∑_{r<q} (∑_{n≤N, n%q=r} a n)^2 ≤ C_LS * ∑_{n≤N} (a n)^2
      (large sieve, residue-filtered squares)

  These are exactly the shapes we will compose with DPS and, later,
  Cauchy–Schwarz on the heavy-set average.
-/
import Mathlib
import Sieve.Analytic.BVFirstIneq

noncomputable section
open Classical

namespace Sieve
namespace Analytic

/-- Residue-block partial sum: sum of `a` over `n ≤ N` with `n % q = r`. -/
@[inline] def residueBlockSum (q N : ℕ) (a : ℕ → ℝ) (r : ℕ) : ℝ :=
  ∑ n ∈ (Finset.range (N + 1)).filter (fun n => n % q = r), a n

/-- Residue partition in filtered form (stable name/shape). -/
lemma sum_residueBlocks_eq_total
    (N q : ℕ) (hq : 0 < q) (a : ℕ → ℝ) :
    (∑ r ∈ Finset.range q, residueBlockSum q N a r)
      = ∑ n ∈ Finset.range (N + 1), a n := by
  classical
  -- Unfold and apply the canonical identity.
  unfold residueBlockSum
  exact residue_chain_identity N q hq a

/-- Large-sieve inequality on residue-block squares (stable name/shape). -/
lemma ls_on_residueBlocks
    (TB : BVToolboxProgressionsSig) (q N : ℕ) (a : ℕ → ℝ) :
    (∑ r ∈ Finset.range q, (residueBlockSum q N a r) ^ 2)
      ≤ TB.C_LS * (∑ n ∈ Finset.range (N + 1), (a n) ^ 2) := by
  classical
  unfold residueBlockSum
  exact ls_chain_bound TB q N a

/-- Tiny compile-touch to keep surfaces warm. -/
theorem bvfirst_chain_compiles (TB : BVToolboxProgressionsSig) : True := by
  let _ := sum_residueBlocks_eq_total 5 3 (by decide) (fun n => (n : ℝ))
  let _ := ls_on_residueBlocks TB 4 6 (fun _ => (1 : ℝ))
  exact True.intro

end Analytic
end Sieve
