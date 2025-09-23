/-
  Sieve/Analytic/OrthogonalityIdentityImpl.lean
  UTF-8 (no BOM), ASCII-only.

  Concrete implementation of `OrthogonalityIdentity`:
    For 0 ≤ r < q,  ∑_{n=0}^{q-1} 1_{n ≡ r [q]} = 1  (over ℝ).

  Idea: for n ∈ range q we have n % q = n, so the indicator becomes `if n = r then 1 else 0`,
  and the sum over `range q` collapses by `Finset.sum_ite_eq`.
-/
import Mathlib
import Sieve.Analytic.BVToolboxSpec

noncomputable section
open Classical
open scoped BigOperators

namespace Sieve
namespace Analytic

/-- For `r < q`, the sum of the residue-`r` indicator over `0..q-1` equals `1`. -/
private lemma sum_indicator_residue_one (q r : ℕ) (hr : r < q) :
    (∑ n ∈ Finset.range q, (if n % q = r then (1 : ℝ) else 0)) = 1 := by
  classical
  -- On 0 ≤ n < q, rewrite `n % q` to `n`.
  have hrewrite :
      (∑ n ∈ Finset.range q, (if n % q = r then (1 : ℝ) else 0))
        = (∑ n ∈ Finset.range q, (if n = r then (1 : ℝ) else 0)) := by
    refine Finset.sum_congr rfl ?_
    intro n hn
    have hnlt : n < q := Finset.mem_range.mp hn
    simp [Nat.mod_eq_of_lt hnlt]
  -- Align orientation of `sum_ite_eq` to `if n = r` using a pointwise rewrite.
  have hflip :
      (∑ n ∈ Finset.range q, (if n = r then (1 : ℝ) else 0))
        = (∑ n ∈ Finset.range q, (if r = n then (1 : ℝ) else 0)) := by
    refine Finset.sum_congr rfl ?_
    intro n hn
    simp [eq_comm]
  -- Sum of a single spike over `range q` collapses.
  have hsum₀ :
      (∑ n ∈ Finset.range q, (if r = n then (1 : ℝ) else 0))
        = (if r ∈ Finset.range q then (1 : ℝ) else 0) :=
    (Finset.sum_ite_eq (s := Finset.range q) (a := r) (b := fun _ => (1 : ℝ)))
  have hsum :
      (∑ n ∈ Finset.range q, (if n = r then (1 : ℝ) else 0))
        = (if r ∈ Finset.range q then (1 : ℝ) else 0) := by
    have h := hsum₀
    -- rewrite the left side from `if r = n` to `if n = r`
    rw [← hflip] at h
    exact h
  have hr_mem : r ∈ Finset.range q := Finset.mem_range.mpr hr
  simp [hrewrite, hsum, hr_mem]

/-- A concrete constructor for `OrthogonalityIdentity` for any `q ≥ 1`. -/
def mkOrthogonalityIdentity (q : ℕ) (hq : 0 < q) : OrthogonalityIdentity :=
{ q := q
  , hq_pos := hq
  , statement := by
      intro r hr
      exact sum_indicator_residue_one q r hr
}

end Analytic
end Sieve
