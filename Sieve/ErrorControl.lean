import Mathlib
open BigOperators Finset

namespace Sieve

/-- Placeholder error term for now: 0. -/
def errorTerm (_H : Finset Nat) (_N : Nat) : Real := 0

@[simp] lemma errorTerm_zero (H : Finset Nat) (N : Nat) :
  errorTerm H N = 0 := rfl

@[simp] lemma errorTerm_nonneg (H : Finset Nat) (N : Nat) :
  0 ≤ errorTerm H N := by
  simp [errorTerm]

end Sieve
