/-
  Sieve/Analytic/IntNatResidueBridge.lean

  Minimal bridge lemmas for residues when mixing ℤ (heavy windows) and ℕ (toolbox lemmas).
  Leaf-only, small, and linter-clean.
-/
import Mathlib

noncomputable section
open Classical

namespace Sieve
namespace Analytic

/-- For `q > 0`, the integer remainder `h % (q : ℤ)` is nonnegative. -/
lemma emod_nonneg_of_nat_pos (h : ℤ) (q : ℕ) (hq : 0 < q) :
    0 ≤ h % (q : ℤ) := by
  have hz : (q : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt hq)
  exact Int.emod_nonneg _ hz

/-- For `q > 0`, the integer remainder `h % (q : ℤ)` is strictly less than `q`. -/
lemma emod_lt_of_nat_pos (h : ℤ) (q : ℕ) (hq : 0 < q) :
    h % (q : ℤ) < (q : ℤ) := by
  have hpos : 0 < (q : ℤ) := by exact_mod_cast hq
  simpa using Int.emod_lt_of_pos h hpos

/-- Shuttle between `ℤ`-equality and `ℕ`-equality on residues. -/
private lemma emod_eq_coe_iff_toNat_eq
    (h : ℤ) (q r : ℕ) (hq : 0 < q) :
    (h % (q : ℤ) = (r : ℤ)) ↔ ((h % (q : ℤ)).toNat = r) := by
  have hnonneg : 0 ≤ h % (q : ℤ) := emod_nonneg_of_nat_pos h q hq
  constructor
  · intro hEq
    have := congrArg Int.toNat hEq
    simp at this
    simpa using this
  · intro hEq
    have hcast : ((h % (q : ℤ)).toNat : ℤ) = (r : ℤ) := by
      simpa using congrArg (fun n : ℕ => (n : ℤ)) hEq
    have hco : ((h % (q : ℤ)).toNat : ℤ) = h % (q : ℤ) := by
      simpa using Int.toNat_of_nonneg hnonneg
    exact hco.symm.trans hcast

/-- Pointwise residue-indicator sum over `ℤ`: collapses to the constant. -/
lemma residue_indicator_sum_pointwise_int
    (q : ℕ) (hq : 0 < q) (h : ℤ) (c : ℝ) :
    (∑ r ∈ Finset.range q, (if h % (q : ℤ) = (r : ℤ) then c else 0)) = c := by
  classical
  -- Rewrite the predicate to a `toNat` form (stays on ℕ indices).
  have h_rewrite :
      (∑ r ∈ Finset.range q, (if h % (q : ℤ) = (r : ℤ) then c else 0))
        = (∑ r ∈ Finset.range q, (if (h % (q : ℤ)).toNat = r then c else 0)) := by
    refine Finset.sum_congr rfl ?_
    intro r hr
    by_cases hEq : h % (q : ℤ) = (r : ℤ)
    · simp [hEq]
    ·
      have hNe' : (h % (q : ℤ)).toNat ≠ r := by
        intro ht
        exact hEq ((emod_eq_coe_iff_toNat_eq h q r hq).mpr ht)
      simp [hEq, hNe']
  -- Turn `if`-sum into a filtered constant sum.
  have h_filter :
      (∑ r ∈ Finset.range q, (if (h % (q : ℤ)).toNat = r then c else 0))
        = ∑ r ∈ (Finset.range q).filter (fun r => (h % (q : ℤ)).toNat = r), c := by
    simpa using
      (Finset.sum_filter
        (s := Finset.range q) (f := fun _ => c)
        (p := fun r => (h % (q : ℤ)).toNat = r)).symm
  -- The filtered set is exactly `{ (h % q).toNat }`.
  have h_nonneg : 0 ≤ h % (q : ℤ) := emod_nonneg_of_nat_pos h q hq
  have h_lt_int : h % (q : ℤ) < (q : ℤ) := emod_lt_of_nat_pos h q hq
  have h_lt_nat : (h % (q : ℤ)).toNat < q := by
    have : ((h % (q : ℤ)).toNat : ℤ) < (q : ℤ) := by
      simpa [Int.toNat_of_nonneg h_nonneg] using h_lt_int
    exact_mod_cast this
  have h_filter_eq :
      (Finset.range q).filter (fun r => (h % (q : ℤ)).toNat = r)
        = { (h % (q : ℤ)).toNat } := by
    apply Finset.ext
    intro r
    constructor
    · intro hr
      rcases Finset.mem_filter.mp hr with ⟨_, hpred⟩
      -- turn membership into equality, no `simpa`
      have hreq : r = (h % (q : ℤ)).toNat := hpred.symm
      simp [Finset.mem_singleton, hreq]
    · intro hr
      -- from singleton membership to range membership + predicate
      have hreq : r = (h % (q : ℤ)).toNat := Finset.mem_singleton.mp hr
      have hrange : r ∈ Finset.range q := by
        rcases hreq with rfl
        exact Finset.mem_range.mpr h_lt_nat
      exact Finset.mem_filter.mpr ⟨hrange, by simp [hreq.symm]⟩
  -- Sum a constant over a singleton
  have h_card :
      ((Finset.range q).filter (fun r => (h % (q : ℤ)).toNat = r)).card = 1 := by
    simp [h_filter_eq]
  have h_sum_const :
      (∑ _r ∈ (Finset.range q).filter (fun r => (h % (q : ℤ)).toNat = r), c)
        = ((Finset.range q).filter (fun r => (h % (q : ℤ)).toNat = r)).card • c := by
    simp [Finset.sum_const, nsmul_eq_mul, mul_comm]
  -- Stitch and conclude: `E = card•c` and `card = 1`, so `E = c`.
  have hfinal :
      (∑ r ∈ Finset.range q, (if h % (q : ℤ) = (r : ℤ) then c else 0))
        = ((Finset.range q).filter (fun r => (h % (q : ℤ)).toNat = r)).card • c := by
    simp [h_rewrite, h_filter, h_sum_const]
  have hcollapse :
      ((Finset.range q).filter (fun r => (h % (q : ℤ)).toNat = r)).card • c = c := by
    simp [h_card]
  exact hfinal.trans hcollapse

/-- Smoke: the bridge lemmas are available in the shape we expect. -/
theorem int_nat_residue_bridge_compiles : True := by
  have _ := emod_nonneg_of_nat_pos (h := (37 : ℤ)) (q := 5) (hq := by decide)
  have _ := emod_lt_of_nat_pos     (h := (37 : ℤ)) (q := 5) (hq := by decide)
  have _ := residue_indicator_sum_pointwise_int (q := 5) (hq := by decide) (h := 37) (c := (2 : ℝ))
  exact True.intro

end Analytic
end Sieve
