import Mathlib

noncomputable section

namespace Sieve
namespace Analytic

/-- Minimal BV/EH constants ledger (safe placeholder; we can extend later). -/
structure BVParams where
  /-- Height with `N ≥ 2`; positivity of `log N` is carried as data. -/
  N : ℕ
  hN2 : 2 ≤ N
  /-- Constants for `Cmain - Cerr1/log N - Cerr2/(log N)^2`. -/
  Cmain : ℝ
  Cerr1 : ℝ
  Cerr2 : ℝ
  /-- Demo threshold carried to Stage-3 wiring. -/
  threshold : ℝ
  /-- Positivity of `log N` provided as data to keep this leaf lightweight. -/
  logN_pos : 0 < Real.log (N : ℝ)

namespace BVParams

/-- Shorthand for `log N`. -/
def logN (P : BVParams) : ℝ :=
  Real.log (P.N : ℝ)

/-- Lower-bound formula used to feed Stage-2/3. -/
def lowerFormula (P : BVParams) : ℝ :=
  P.Cmain - (P.Cerr1 / P.logN) - (P.Cerr2 / (P.logN) ^ 2)

/-- Rewrites `a - b - c = a - (b + c)` for this specific formula. -/
lemma lowerFormula_eq_sub_add (P : BVParams) :
    P.lowerFormula
      = P.Cmain - ((P.Cerr1 / P.logN) + (P.Cerr2 / (P.logN) ^ 2)) := by
  simp [lowerFormula, sub_eq_add_neg, add_comm, add_assoc]

/-- Trivial upper bound assuming `Cerr1, Cerr2 ≥ 0`. -/
lemma lowerFormula_le_Cmain (P : BVParams)
    (hC1 : 0 ≤ P.Cerr1) (hC2 : 0 ≤ P.Cerr2) :
    P.lowerFormula ≤ P.Cmain := by
  have hlogpos : 0 < P.logN := P.logN_pos
  have h1 : 0 ≤ P.Cerr1 / P.logN :=
    div_nonneg hC1 (le_of_lt hlogpos)
  have hsq : 0 ≤ (P.logN) ^ 2 := by
    simpa using (sq_nonneg (P.logN))
  have h2 : 0 ≤ P.Cerr2 / (P.logN) ^ 2 :=
    div_nonneg hC2 hsq
  have hsum : 0 ≤ (P.Cerr1 / P.logN) + (P.Cerr2 / (P.logN) ^ 2) := add_nonneg h1 h2
  simpa [lowerFormula_eq_sub_add] using sub_le_self P.Cmain hsum

end BVParams

end Analytic
end Sieve
