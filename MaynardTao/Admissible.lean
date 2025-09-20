import Mathlib

/-!
MaynardTao/Admissible.lean
--------------------------
A minimal admissibility predicate for a finite set of shifts `H`.

Definition:
* `IsAdmissible H` means: for every prime `p`, not all residues mod `p` are
  represented by `H` — i.e. the image of `H` in `ZMod p` has cardinality `< p`.

This is structural and sorry-free; wiring into `BoundedGaps.Spec` will come later.
-/

namespace MaynardTao
namespace Admissible

open scoped BigOperators

/-- For a prime `p`, the set of residues modulo `p` hit by `H`. -/
def residuesMod (H : Finset ℤ) (p : ℕ) : Finset (ZMod p) :=
  H.image (fun h => ((h : ℤ) : ZMod p))

@[simp] lemma residuesMod_mem {H : Finset ℤ} {p : ℕ} {a : ZMod p} :
    a ∈ residuesMod H p ↔ ∃ h ∈ H, ((h : ℤ) : ZMod p) = a := by
  classical
  unfold residuesMod
  simp

/-- A finite shift set `H` is admissible if for every prime `p`,
    not all residue classes mod `p` are covered. -/
def IsAdmissible (H : Finset ℤ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → (residuesMod H p).card < p

end Admissible
end MaynardTao
