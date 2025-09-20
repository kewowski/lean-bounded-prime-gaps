/-
  Sieve/Examples.lean
  UTF-8 (no BOM), ASCII-only.
-/
import Mathlib
import Character.Decompositions
import Sieve.AdmissibleTuples
import Sieve.Pipeline
import Sieve.Contracts
import Sieve.NaiveWeight

noncomputable section
open Classical

namespace Sieve.Examples

/-- A singleton `{a}` can never be surjective onto `ZMod p` for prime `p`,
    so it is admissible. -/
lemma admissible_singleton (a : ℤ) :
    Sieve.AdmissibleTuples.Admissible ({a} : Finset ℤ) := by
  intro p hp hsurj
  -- `ZMod p` is nontrivial since `hp.one_lt : 1 < p`
  haveI : Fact (1 < p) := ⟨hp.one_lt⟩
  -- Surjectivity on 0 and 1 residues
  have hx := hsurj (0 : ZMod p)
  have hy := hsurj (1 : ZMod p)
  rcases hx with ⟨h0, h0mem, h0eq⟩
  rcases hy with ⟨h1, h1mem, h1eq⟩
  -- Both witnesses must be `a`, since the set is a singleton
  have h0a : h0 = a := by simpa using (Finset.mem_singleton.mp h0mem)
  have h1a : h1 = a := by simpa using (Finset.mem_singleton.mp h1mem)
  -- Then `(a : ZMod p)` equals both 0 and 1, contradiction.
  have : (1 : ZMod p) = 0 := by
    calc
      (1 : ZMod p)
          = (h1 : ZMod p) := by simpa [h1a] using h1eq.symm
      _   = (a  : ZMod p) := by simp [h1a]
      _   = (h0 : ZMod p) := by simp [h0a]
      _   = (0  : ZMod p) := by simpa [h0a] using h0eq
  exact one_ne_zero this

/-- A trivial, always-green pipeline using `{0}` and the conservative contract. -/
def trivialPipeline : Sieve.Pipeline.Config :=
  { chars      := Character.decomp_available
    contract   := Sieve.Contracts.conservativeContract
    tuple      := ({0} : Finset ℤ)
    admissible := admissible_singleton 0 }

end Sieve.Examples

