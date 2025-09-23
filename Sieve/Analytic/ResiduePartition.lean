/-
  Sieve/Analytic/ResiduePartition.lean
  Residue partition identity (indicator form).
-/
import Mathlib

noncomputable section
open Classical

namespace Sieve
namespace Analytic

/-- Sum of a single "if-equals" spike over a finite set (ℝ version):
`∑_{x∈s} (if x = t then c else 0) = (if t∈s then c else 0)`. -/
lemma sum_if_eq_singleton_real
    {α} [DecidableEq α]
    (s : Finset α) (t : α) (c : ℝ) :
    (∑ x ∈ s, (if x = t then c else 0))
      = (if t ∈ s then c else 0) := by
  classical
  -- Convert to a filtered constant-sum.
  have hflip :
      (∑ x ∈ s, (if x = t then c else 0))
        = ∑ x ∈ s.filter (fun x => x = t), c :=
    (Finset.sum_filter (s := s) (f := fun _ => c) (p := fun x => x = t)).symm
  -- Split by membership of `t` in `s`.
  by_cases ht : t ∈ s
  · -- The filter is `{t}`.
    have hfilter : s.filter (fun x => x = t) = ({t} : Finset α) := by
      ext x; constructor
      · intro hx
        rcases Finset.mem_filter.mp hx with ⟨hxS, hxEq⟩
        exact Finset.mem_singleton.mpr hxEq
      · intro hx
        have hxEq : x = t := Finset.mem_singleton.mp hx
        have hxS : x ∈ s := by exact hxEq ▸ ht
        exact Finset.mem_filter.mpr ⟨hxS, hxEq⟩
    calc
      (∑ x ∈ s, (if x = t then c else 0))
          = ∑ x ∈ s.filter (fun x => x = t), c := hflip
      _   = ∑ _x ∈ ({t} : Finset α), c := by
        simp [hfilter]
      _   = c := by
        simp
      _   = (if t ∈ s then c else 0) := by
        simp [ht]
  · -- The filter is empty.
    have hfilter0 : s.filter (fun x => x = t) = (∅ : Finset α) := by
      refine Finset.filter_eq_empty_iff.mpr ?noneEq
      intro x hx hxEq
      have : t ∈ s := by exact hxEq ▸ hx
      exact (ht this).elim
    calc
      (∑ x ∈ s, (if x = t then c else 0))
          = ∑ x ∈ s.filter (fun x => x = t), c := hflip
      _   = 0 := by simp [hfilter0]
      _   = (if t ∈ s then c else 0) := by simp [ht]

/-- **Residue partition (indicator form).**
For `q > 0`, the residue blocks partition `range (N+1)`:
\[
  \sum_{r < q} \ \sum_{n \le N} [n \% q = r]\; f(n)
   \;=\; \sum_{n \le N} f(n).
\]
-/
lemma residue_partition_indicator
    (N q : ℕ) (hq : 0 < q) (f : ℕ → ℝ) :
    (∑ r ∈ Finset.range q,
        ∑ n ∈ Finset.range (N + 1),
          (if n % q = r then f n else 0))
      = ∑ n ∈ Finset.range (N + 1), f n := by
  classical
  -- Swap the two finite sums.
  have hswap :
      (∑ r ∈ Finset.range q,
          ∑ n ∈ Finset.range (N + 1),
            (if n % q = r then f n else 0))
        = (∑ n ∈ Finset.range (N + 1),
            ∑ r ∈ Finset.range q,
              (if n % q = r then f n else 0)) :=
    Finset.sum_comm
  -- Compute the inner sum in `r` pointwise for each `n`.
  have hinner :
      ∀ n, (∑ r ∈ Finset.range q,
               (if n % q = r then f n else 0))
            = f n := by
    intro n
    -- Rewrite guard to `r = n % q`.
    have hswapPred :
        (∑ r ∈ Finset.range q, (if n % q = r then f n else 0))
          = (∑ r ∈ Finset.range q, (if r = n % q then f n else 0)) := by
      refine Finset.sum_congr rfl ?_
      intro r _hr
      by_cases h : r = n % q
      · simp [h]
      ·
        -- from r ≠ n%q get n%q ≠ r (no `simpa`)
        have h' : n % q ≠ r := fun h'' => h h''.symm
        simp [h, h']
    -- Apply the singleton lemma with `s = range q`, `t = n % q`.
    have hsum :
        (∑ r ∈ Finset.range q, (if r = n % q then f n else 0))
          = (if n % q ∈ Finset.range q then f n else 0) :=
      sum_if_eq_singleton_real (Finset.range q) (n % q) (f n)
    -- And `n % q ∈ range q` since `q > 0`.
    have hmem : n % q ∈ Finset.range q :=
      Finset.mem_range.mpr (Nat.mod_lt n hq)
    have hR : (if n % q ∈ Finset.range q then f n else 0) = f n := by
      simp [hmem]
    exact hswapPred.trans (hsum.trans hR)
  -- Assemble.
  calc
    (∑ r ∈ Finset.range q,
        ∑ n ∈ Finset.range (N + 1),
          (if n % q = r then f n else 0))
        = (∑ n ∈ Finset.range (N + 1),
            ∑ r ∈ Finset.range q,
              (if n % q = r then f n else 0)) := hswap
    _ = ∑ n ∈ Finset.range (N + 1), f n := by
      refine Finset.sum_congr rfl ?_
      intro n _hn
      exact hinner n

/-- Tiny compile-touch so CI keeps this surface hot. -/
theorem residue_partition_compiles : True := by
  let _ := residue_partition_indicator 5 3 (by decide) (fun n => (n : ℝ))
  exact True.intro

end Analytic
end Sieve
