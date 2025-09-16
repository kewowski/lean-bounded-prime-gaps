import Mathlib
import MaynardTao.Admissible

/-!
MaynardTao/AdmissibleLemmas.lean
--------------------------------
Basic facts for the structural admissibility predicate:

* `residuesMod_subset_of_subset` : image mod p is monotone in `H`
* `admissible_mono`              : admissibility is downward-closed (subset)
* `admissible_empty`             : the empty set is admissible
-/

namespace MaynardTao
namespace Admissible

open scoped BigOperators

/-- If `H₁ ⊆ H₂` then the residues hit modulo `p` satisfy
    `residuesMod H₁ p ⊆ residuesMod H₂ p`. -/
lemma residuesMod_subset_of_subset
    {H₁ H₂ : Finset ℤ} (hsub : H₁ ⊆ H₂) (p : ℕ) :
    residuesMod H₁ p ⊆ residuesMod H₂ p := by
  classical
  intro a ha
  rcases (residuesMod_mem (H := H₁) (p := p)).1 ha with ⟨h, hh1, rfl⟩
  exact (residuesMod_mem (H := H₂) (p := p)).2 ⟨h, hsub hh1, rfl⟩

/-- Admissibility is downward-closed: if `H₂` is admissible and `H₁ ⊆ H₂`,
    then `H₁` is admissible. -/
lemma admissible_mono {H₁ H₂ : Finset ℤ}
    (hAdm : IsAdmissible H₂) (hsub : H₁ ⊆ H₂) :
    IsAdmissible H₁ := by
  classical
  intro p hp
  have hsubset := residuesMod_subset_of_subset (H₁ := H₁) (H₂ := H₂) hsub p
  have hcard_mono :
      (residuesMod H₁ p).card ≤ (residuesMod H₂ p).card :=
    Finset.card_mono hsubset
  exact lt_of_le_of_lt hcard_mono (hAdm p hp)

/-- The empty set is admissible. -/
lemma admissible_empty : IsAdmissible (∅ : Finset ℤ) := by
  intro p hp
  classical
  -- residuesMod ∅ p is empty, so its card is 0 < p for prime p (since p ≥ 2).
  simpa [residuesMod] using (Nat.succ_le_of_lt hp.pos)

end Admissible
end MaynardTao
