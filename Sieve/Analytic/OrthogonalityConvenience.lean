/-
  Sieve/Analytic/OrthogonalityConvenience.lean
  UTF-8 (no BOM), ASCII-only.

  Convenience lemmas around orthogonality-of-residue indicators.
  Adds in-range (=1) and out-of-range (=0) specializations.
-/
import Mathlib
import Sieve.Analytic.BVToolboxProgressionsSig

noncomputable section
open Classical

namespace Sieve
namespace Analytic

/-- Canonical orthogonality (exactly the toolbox shape, re-exposed). -/
lemma orthogonality_canonical
    (TB : BVToolboxProgressionsSig) (q r : ℕ) :
    (∑ n ∈ Finset.range q, (if n % q = r then (1 : ℝ) else 0))
      = (if r ∈ Finset.range q then (1 : ℝ) else 0) :=
  TB.orthogonality_indicator q r

/-- If `r < q`, the indicator sum across `n ∈ [0..q-1]` is `1`. -/
lemma orthogonality_in_range_one
    (TB : BVToolboxProgressionsSig) {q r : ℕ} (hr : r < q) :
    (∑ n ∈ Finset.range q, (if n % q = r then (1 : ℝ) else 0)) = 1 := by
  classical
  have h := TB.orthogonality_indicator q r
  have hrmem : r ∈ Finset.range q := Finset.mem_range.mpr hr
  have hR : (if r ∈ Finset.range q then (1 : ℝ) else 0) = 1 := by
    simp [hrmem]
  calc
    (∑ n ∈ Finset.range q, (if n % q = r then (1 : ℝ) else 0))
        = (if r ∈ Finset.range q then (1 : ℝ) else 0) := h
    _   = 1 := hR

/-- If `r ≥ q`, the indicator sum across `n ∈ [0..q-1]` is `0`. -/
lemma orthogonality_out_of_range_zero
    (TB : BVToolboxProgressionsSig) {q r : ℕ} (hr : q ≤ r) :
    (∑ n ∈ Finset.range q, (if n % q = r then (1 : ℝ) else 0)) = 0 := by
  classical
  have h := TB.orthogonality_indicator q r
  have hrnot : r ∉ Finset.range q := by
    have hnl : ¬ r < q := not_lt.mpr hr
    simp [Finset.mem_range, hnl]
  have hR0 : (if r ∈ Finset.range q then (1 : ℝ) else 0) = 0 := by
    simp [hrnot]
  calc
    (∑ n ∈ Finset.range q, (if n % q = r then (1 : ℝ) else 0))
        = (if r ∈ Finset.range q then (1 : ℝ) else 0) := h
    _   = 0 := hR0

/-- Availability sanity: make sure this file is “hot” for CI. -/
theorem orthogonality_convenience_compiles
    (TB : BVToolboxProgressionsSig) : True := by
  let _ := orthogonality_canonical TB (q := 3) (r := 1)
  let _ := orthogonality_in_range_one TB (q := 4) (r := 2) (hr := by decide)
  let _ := orthogonality_out_of_range_zero TB (q := 2) (r := 5) (hr := by decide)
  exact True.intro

end Analytic
end Sieve
