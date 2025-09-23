/-
  Sieve/Analytic/ResidueFilterIndicator.lean
  Leaf corollaries that match LS/DPS shapes:

  (1) `residue_filter_to_indicator`:
      ∑_{n ≤ N, n%q=r} a(n) = ∑_{n ≤ N} [n%q=r]·a(n)

  (2) `residue_partition_filtered`:
      ∑_{r<q} ∑_{n ≤ N, n%q=r} a(n) = ∑_{n ≤ N} a(n)
-/
import Mathlib
import Sieve.Analytic.ResiduePartition

noncomputable section
open Classical

namespace Sieve
namespace Analytic

/-- Convert a residue-class **filtered** sum to an **indicator** sum.
Shape matches large-sieve / DPS conveniences. -/
lemma residue_filter_to_indicator
    (N q r : ℕ) (a : ℕ → ℝ) :
    (∑ n ∈ (Finset.range (N + 1)).filter (fun n => n % q = r), a n)
      = ∑ n ∈ Finset.range (N + 1), (if n % q = r then a n else 0) := by
  classical
  -- Directly apply `sum_filter` with `s = range (N+1)` and predicate `p n := (n%q=r)`.
  simpa using
    (Finset.sum_filter
      (s := Finset.range (N + 1))
      (f := a)
      (p := fun n => n % q = r))

/-- Residue partition in the **filtered** form used by LS:
\[
  \sum_{r<q} \ \sum_{n\le N,\, n\%q=r} a(n)
  \;=\; \sum_{n\le N} a(n), \quad (q>0).
\]
-/
lemma residue_partition_filtered
    (N q : ℕ) (hq : 0 < q) (a : ℕ → ℝ) :
    (∑ r ∈ Finset.range q,
        ∑ n ∈ (Finset.range (N + 1)).filter (fun n => n % q = r), a n)
      = ∑ n ∈ Finset.range (N + 1), a n := by
  classical
  -- Rewrite inner sums via the filter↔indicator lemma, then invoke the indicator partition.
  have hstep :
      (∑ r ∈ Finset.range q,
          ∑ n ∈ (Finset.range (N + 1)).filter (fun n => n % q = r), a n)
        = (∑ r ∈ Finset.range q,
            ∑ n ∈ Finset.range (N + 1),
              (if n % q = r then a n else 0)) := by
    refine Finset.sum_congr rfl ?_
    intro r _hr
    exact residue_filter_to_indicator N q r a
  -- Now use the indicator-form partition lemma.
  have hpart := residue_partition_indicator N q hq a
  -- Assemble.
  exact hstep.trans hpart

/-- Tiny compile-touch. -/
theorem residue_filter_indicator_compiles : True := by
  let _ := residue_filter_to_indicator 4 3 1 (fun n => (n : ℝ))
  let _ := residue_partition_filtered 5 2 (by decide) (fun _ => (1 : ℝ))
  exact True.intro

end Analytic
end Sieve
