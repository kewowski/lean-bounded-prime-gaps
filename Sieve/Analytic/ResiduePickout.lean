/-
  Sieve/Analytic/ResiduePickout.lean
  Clean "pickout" lemmas for sums over all residues modulo `q+1`.

  These are tiny utilities used throughout the analytic scaffolding to
  collapse a residue-class indicator when summing over all residues.
-/
import Mathlib
import Sieve.Analytic.ResidueSumBasics

noncomputable section
open Classical BigOperators

namespace Sieve
namespace Analytic

/--
Pickout over all residues (ℂ-valued): for any `g : ZMod (q+1) → ℂ`,
`∑_r if (n ≡ r) then g r else 0 = g n`.
-/
theorem pickout_zmod_complex
    (q n : ℕ) (g : ZMod q.succ → ℂ) :
    (∑ r : ZMod q.succ,
        (if ((n : ZMod q.succ) = r) then g r else 0))
      = g (n : ZMod q.succ) := by
  classical
  -- Turn the Fintype sum into a sum over `univ` and pick out the unique term.
  have hu :
      (∑ r ∈ (Finset.univ : Finset (ZMod q.succ)),
          (if ((n : ZMod q.succ) = r) then g r else 0))
        = g (n : ZMod q.succ) := by
    refine Finset.sum_eq_single (n : ZMod q.succ) ?hmem ?hrest
    · simp
    · intro r hr hne; simp [hne.symm]
  simpa using hu

/-- Symmetric equality-check variant (ℂ-valued). -/
theorem pickout_zmod_complex_eq
    (q n : ℕ) (g : ZMod q.succ → ℂ) :
    (∑ r : ZMod q.succ,
        (if (r = (n : ZMod q.succ)) then g r else 0))
      = g (n : ZMod q.succ) := by
  classical
  simpa [eq_comm] using pickout_zmod_complex q n g

/-- Constant pickout over all residues (ℂ): the indicator sums to the constant. -/
theorem pickout_zmod_const_complex
    (q n : ℕ) (c : ℂ) :
    (∑ r : ZMod q.succ,
        (if ((n : ZMod q.succ) = r) then c else 0)) = c := by
  classical
  -- Specialize the general lemma with `g ≡ (fun _ => c)`.
  simpa using pickout_zmod_complex q n (fun _ => c)

/-- Constant pickout over all residues (ℝ): the indicator sums to the constant. -/
theorem pickout_zmod_const_real
    (q n : ℕ) (c : ℝ) :
    (∑ r : ZMod q.succ,
        (if ((n : ZMod q.succ) = r) then c else 0)) = c := by
  classical
  have hu :
      (∑ r ∈ (Finset.univ : Finset (ZMod q.succ)),
          (if ((n : ZMod q.succ) = r) then c else 0)) = c := by
    refine Finset.sum_eq_single (n : ZMod q.succ) ?hmem ?hrest
    · simp
    · intro r hr hne; simp [hne.symm]
  simpa using hu

end Analytic
end Sieve
