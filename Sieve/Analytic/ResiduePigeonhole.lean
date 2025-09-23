/-
  Sieve/Analytic/ResiduePigeonhole.lean

  Pigeonhole over residues:
  Among the residue blocks modulo q, one block carries at least the average mass.
-/
import Mathlib
import Sieve.Analytic.BVFirstChainBound

noncomputable section
open Classical

namespace Sieve
namespace Analytic

/-- Generic: on a nonempty finite set, some point attains at least the average of `f`. -/
private lemma exists_ge_avg_over_range
    (q : ℕ) (hq : 0 < q) (f : ℕ → ℝ) :
    ∃ r ∈ Finset.range q,
      (∑ r ∈ Finset.range q, f r) / (q : ℝ) ≤ f r := by
  classical
  -- nonempty since q > 0 ⇒ 0 ∈ range q
  have hne : (Finset.range q).Nonempty := ⟨0, Finset.mem_range.mpr hq⟩
  obtain ⟨r, hr, hmax⟩ := Finset.exists_max_image (Finset.range q) f hne
  -- sum ≤ card * max
  have hsum_le_const :
      (∑ r' ∈ Finset.range q, f r') ≤ ∑ _r' ∈ Finset.range q, f r :=
    Finset.sum_le_sum (by intro r' hr'; exact hmax r' hr')
  have hsum_le :
      (∑ r' ∈ Finset.range q, f r')
        ≤ (Finset.card (Finset.range q) : ℝ) * f r := by
    simpa [Finset.sum_const, nsmul_eq_mul] using hsum_le_const
  -- divide by positive q
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast hq
  have hdiv :
      (∑ r' ∈ Finset.range q, f r') / (q : ℝ)
        ≤ ((Finset.card (Finset.range q) : ℝ) * f r) / (q : ℝ) :=
    div_le_div_of_nonneg_right hsum_le (le_of_lt hqpos)
  -- rewrite card(range q) = q, then cancel q
  have hdiv' :
      (∑ r' ∈ Finset.range q, f r') / (q : ℝ)
        ≤ ((q : ℝ) * f r) / (q : ℝ) := by
    simpa [Finset.card_range] using hdiv
  have hqne : (q : ℝ) ≠ 0 := ne_of_gt hqpos
  have rhs_eq : ((q : ℝ) * f r) / (q : ℝ) = f r := by
    calc
      ((q : ℝ) * f r) / (q : ℝ)
          = (f r * (q : ℝ)) / (q : ℝ) := by simp [mul_comm]
      _ = f r * ((q : ℝ) / (q : ℝ)) := by simp [mul_div_assoc]
      _ = f r := by simp [div_self hqne]
  exact ⟨r, hr, by simpa [rhs_eq] using hdiv'⟩

/-- **Pigeonhole over residues (filtered form).**
For `q > 0`, there exists `r < q` such that the residue-block sum at `r` is at least
the average over all residues, which equals `(∑_{n≤N} a n) / q`. -/
lemma exists_residue_with_block_ge_avg
    (N q : ℕ) (hq : 0 < q) (a : ℕ → ℝ) :
    ∃ r ∈ Finset.range q,
      (∑ n ∈ Finset.range (N + 1), a n) / (q : ℝ)
        ≤ residueBlockSum q N a r := by
  classical
  -- Apply "max ≥ average" to residueBlockSum
  obtain ⟨r, hr, havg⟩ :=
    exists_ge_avg_over_range q hq (fun r => residueBlockSum q N a r)
  -- Rewrite total sum with residue partition identity
  have hsum :
      (∑ r' ∈ Finset.range q, residueBlockSum q N a r')
        = ∑ n ∈ Finset.range (N + 1), a n :=
    sum_residueBlocks_eq_total N q hq a
  exact ⟨r, hr, by simpa [hsum] using havg⟩

/-- Tiny compile-touch. -/
theorem residue_pigeonhole_compiles : True := by
  let _ := exists_residue_with_block_ge_avg 5 3 (by decide) (fun n => (n : ℝ))
  exact True.intro

end Analytic
end Sieve
