/-
  Sieve/AdmissibleTwin.lean
  Twin tuple {0,2} is admissible (surjectivity-style, translation to {-1,1}).
-/
import Mathlib
import Sieve.AdmissibleTuples
-- Optional: export a pipeline config that uses the conservative Gallagher hook.
import Sieve.Pipeline
import Sieve.GallagherHook

-- Silence harmless "try `simp` instead of `simpa`" hints in this file.
set_option linter.unnecessarySimpa false

noncomputable section
open Classical

namespace Sieve
namespace AdmissibleTwin

open Sieve.AdmissibleTuples

/-- The twin tuple {0,2}. -/
def twin : Finset ℤ := {0, 2}

/-- `translate twin (-1)` never hits residue `0` mod a prime `p`,
so it cannot cover all residues. -/
private lemma not_covers_zero_of_translate_twin
  (p : ℕ) (hp : p.Prime) :
  ¬ coversAllResiduesMod (translate twin (-1)) p := by
  classical
  -- Make `ZMod p` nontrivial (so `1 ≠ 0` is available).
  haveI : Fact (1 < p) := ⟨hp.one_lt⟩
  intro hsurj
  -- Surjectivity at 0 gives some h with (h : ZMod p) = 0.
  obtain ⟨h, hh, h0⟩ := hsurj 0
  rcases Finset.mem_image.mp hh with ⟨k, hk, rfl⟩
  have hk' : k = 0 ∨ k = 2 := by
    simpa [twin, Finset.mem_insert, Finset.mem_singleton] using hk
  -- From the two possibilities for k, deduce (1 : ZMod p) = 0, contradiction.
  have h10 : (1 : ZMod p) = 0 := by
    rcases hk' with rfl | rfl
    · -- k = 0 ⇒ h = -1 ⇒ ((-1 : ZMod p)) = 0; add 1 ⇒ 1 = 0.
      have : ((-1 : ℤ) : ZMod p) = 0 := by simpa using h0
      have := congrArg (fun y : ZMod p => (1 : ZMod p) + y) this
      -- LHS: 1 + (-1) = 0, RHS: 1 + 0 = 1
      simpa using this.symm
    · -- k = 2 ⇒ h = 1 ⇒ ((1 : ZMod p)) = 0 directly.
      simpa using h0
  exact one_ne_zero h10

/-- Admissibility of the twin tuple `{0,2}`. -/
lemma admissible_twin : AdmissibleTuples.Admissible twin := by
  classical
  -- First, the translated tuple is admissible by the lemma above.
  have htrans :
      AdmissibleTuples.Admissible (AdmissibleTuples.translate twin (-1)) := by
    intro p hp; exact not_covers_zero_of_translate_twin p hp
  -- Transport back by translation invariance.
  have := (AdmissibleTuples.admissible_translate_iff twin (-1)).1 htrans
  simpa using this

/-- Optional: a ready-to-run pipeline config using the conservative Gallagher hook. -/
def twinConfig : Sieve.Pipeline.Config :=
{ chars      := Character.decomp_available,
  contract   := Sieve.GallagherHook.contract,
  tuple      := twin,
  admissible := admissible_twin }

end AdmissibleTwin
end Sieve
