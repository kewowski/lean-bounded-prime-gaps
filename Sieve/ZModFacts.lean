/-
  Sieve/ZModFacts.lean
  Small, stable facts about `ZMod p` for prime `p`.
-/
import Mathlib

noncomputable section
open Classical

namespace Sieve.ZModFacts

/-- In `ZMod p` with `p` prime, we have `0 ≠ 1`. -/
lemma zero_ne_one_of_prime {p : ℕ} (hp : p.Prime) : (0 : ZMod p) ≠ 1 := by
  -- `Fact (0 < p)` gives a nontrivial `ZMod p`.
  haveI : Fact (0 < p) := ⟨hp.pos⟩
  simpa using (zero_ne_one (α := ZMod p))

/-- In `ZMod p` with `p` prime, we have `1 ≠ 0`. -/
lemma one_ne_zero_of_prime {p : ℕ} (hp : p.Prime) : (1 : ZMod p) ≠ 0 := by
  haveI : Fact (0 < p) := ⟨hp.pos⟩
  simpa using (one_ne_zero (α := ZMod p))

/-- In any nontrivial ring, `(-1) ≠ 0`. For `ZMod p` with `p` prime, this holds. -/
lemma neg_one_ne_zero_of_prime {p : ℕ} (hp : p.Prime) : ((-1 : ZMod p) ≠ 0) := by
  haveI : Fact (0 < p) := ⟨hp.pos⟩
  -- If `-1 = 0`, adding 1 gives `0 = 1`.
  intro h
  have : (0 : ZMod p) = 1 := by
    have := congrArg (fun x : ZMod p => x + (1 : ZMod p)) h
    simpa using this
  exact (zero_ne_one_of_prime hp) this

end Sieve.ZModFacts
