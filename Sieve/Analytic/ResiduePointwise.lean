/-
  Sieve/Analytic/ResiduePointwise.lean

  Pointwise orthogonality in our canonical orientation:
    ∑_{r<q} 1_{n%q=r} · c = c   (for q>0)
-/
import Mathlib

noncomputable section
open Classical

namespace Sieve
namespace Analytic

/-- For `q > 0`, the residue-class indicators over `r < q` sum to `c`:
\[
  \sum_{r<q} \mathbf{1}_{n\bmod q = r}\, c \;=\; c.
\]
Canonical binder order: `if n % q = r then c else 0`. -/
lemma residue_indicator_sum_pointwise
    (q n : ℕ) (hq : 0 < q) (c : ℝ) :
    (∑ r ∈ Finset.range q, (if n % q = r then c else 0)) = c := by
  classical
  -- Rewrite sum of indicators as a filtered constant sum.
  have h_filter :
      (∑ r ∈ Finset.range q, (if n % q = r then c else 0))
        = ∑ r ∈ (Finset.range q).filter (fun r => n % q = r), c := by
    -- `∑_{x∈s} ite (p x) (f x) 0 = ∑_{x∈s.filter p} f x`
    exact
      (Finset.sum_filter
        (s := Finset.range q) (f := fun _ => c) (p := fun r => n % q = r)).symm
  -- The filtered set is exactly `{n % q}` since `n % q ∈ range q`.
  have hmem : n % q ∈ Finset.range q := by
    exact Finset.mem_range.mpr (Nat.mod_lt n hq)
  have hset :
      (Finset.range q).filter (fun r => n % q = r) = { n % q } := by
    apply Finset.ext
    intro r
    constructor
    · intro hr
      rcases Finset.mem_filter.mp hr with ⟨hrng, hpeq⟩
      -- If `n%q = r`, then `r` is exactly the singleton element.
      -- `Finset.mem_singleton` expects `r = n%q`.
      exact (Finset.mem_singleton.mpr hpeq.symm)
    · intro hr
      -- From r ∈ {n%q}, we get r = n%q.
      have hr_eq : r = n % q := Finset.mem_singleton.mp hr
      -- r ∈ range q follows from hmem by rewriting r = n%q
      have rmem : r ∈ Finset.range q := by
        simpa [hr_eq] using hmem
      -- And the predicate `n % q = r` holds by symmetry.
      have heq : n % q = r := hr_eq.symm
      -- Package as membership in the filter.
      exact Finset.mem_filter.mpr ⟨rmem, heq⟩
  -- Sum over a singleton is `c`.
  have h_sum :
      (∑ r ∈ (Finset.range q).filter (fun r => n % q = r), c) = c := by
    simp [hset]
  -- Assemble.
  exact h_filter.trans h_sum

/-- Tiny compile-touch. -/
theorem residue_pointwise_compiles : True := by
  let _ := residue_indicator_sum_pointwise 3 7 (by decide) (2 : ℝ)
  exact True.intro

end Analytic
end Sieve
