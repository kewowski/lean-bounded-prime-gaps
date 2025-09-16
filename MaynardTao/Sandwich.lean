import Mathlib
import MaynardTao.Inequalities
import MaynardTao.PrimeCounts
import MaynardTao.Sums
import MaynardTao.ShiftPrimes
import MaynardTao.BoundedGaps

/-!
MaynardTao/Sandwich.lean
------------------------
Bundle the global lower/upper bounds:

  (r : ℚ) * S_atLeast ≤ S' ≤ (H.card : ℚ) * S0

Both in raw form and Spec form.
-/

namespace MaynardTao
namespace Sandwich

open scoped BigOperators

variable {P : WeightParams}

/-- Left inequality: `(r : ℚ) * S_{≥ r} ≤ S'`. -/
lemma left (W : SieveWeight P) (N : ℕ) (H : Finset ℤ) (r : ℕ) :
    (r : ℚ) * PrimeCounts.S_atLeast (W := W) N H r
      ≤ ShiftPrimes.S_prime (W := W) N H := by
  classical
  -- from RCrit_all: S' ≥ (r : ℚ) * S_atLeast
  have h := Inequalities.RCrit_all (W := W) N H r
  simpa [Inequalities.RCrit, ge_iff_le] using h

/-- Right inequality: `S' ≤ (H.card : ℚ) * S0`. -/
lemma right (W : SieveWeight P) (N : ℕ) (H : Finset ℤ) :
    ShiftPrimes.S_prime (W := W) N H
      ≤ (H.card : ℚ) * Sums.S0 (W := W) N := by
  classical
  simpa using Inequalities.S_prime_le_cardH_S0 (W := W) N H

/-- Combined sandwich inequality. -/
lemma both (W : SieveWeight P) (N : ℕ) (H : Finset ℤ) (r : ℕ) :
    (r : ℚ) * PrimeCounts.S_atLeast (W := W) N H r
      ≤ ShiftPrimes.S_prime (W := W) N H
      ∧ ShiftPrimes.S_prime (W := W) N H
      ≤ (H.card : ℚ) * Sums.S0 (W := W) N :=
  ⟨left (W := W) N H r, right (W := W) N H⟩

/-- Spec-version: left inequality. -/
lemma spec_left (s : BoundedGaps.Spec) (r : ℕ) :
    (r : ℚ) * PrimeCounts.S_atLeast (W := s.W) s.N s.P.H r
      ≤ s.Sprime := by
  classical
  have h := Inequalities.RCritSpec_all (s := s) r
  simpa [Inequalities.RCritSpec, ge_iff_le] using h

/-- Spec-version: right inequality. -/
lemma spec_right (s : BoundedGaps.Spec) :
    s.Sprime ≤ (s.P.H.card : ℚ) * s.S0 := by
  classical
  simpa using right (W := s.W) s.N s.P.H

/-- Spec-version: combined sandwich inequality. -/
lemma spec_both (s : BoundedGaps.Spec) (r : ℕ) :
    (r : ℚ) * PrimeCounts.S_atLeast (W := s.W) s.N s.P.H r ≤ s.Sprime
    ∧ s.Sprime ≤ (s.P.H.card : ℚ) * s.S0 :=
  ⟨spec_left (s := s) r, spec_right (s := s)⟩

end Sandwich
end MaynardTao
