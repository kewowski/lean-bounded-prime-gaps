/-
  Sieve/Compat/FinsetCard.lean
  Compatibility shim for Finset card monotonicity. Some project files
  refer to `Finset.card_le_of_subset`; we forward that name to the
  current mathlib lemma `Finset.card_mono`.
-/
import Mathlib

noncomputable section
open Classical

namespace Finset

/-- Compatibility: `card_le_of_subset` as an alias to `card_mono`. -/
theorem card_le_of_subset {α} [DecidableEq α] {s t : Finset α}
    (h : s ⊆ t) : s.card ≤ t.card :=
  card_mono h

end Finset
