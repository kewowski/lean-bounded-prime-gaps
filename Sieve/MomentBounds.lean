/-
  Sieve/MomentBounds.lean
  Version-robust wrappers to bound a “first moment” (sum over a finite support).
-/
import Mathlib
import Sieve.SumBounds

noncomputable section
open Classical

namespace Sieve.MomentBounds
open Sieve.SumBounds

/-- A generic “first moment” from raw data: sum of `w` over `supp`. -/
def firstMomentOf (supp : Finset ℤ) (w : ℤ → ℝ) : ℝ :=
  ∑ n ∈ supp, w n

/-- If `w n ≤ M` on `supp`, then `firstMomentOf ≤ (supp.card : ℝ) * M`. -/
lemma firstMomentOf_le_card_mul_bound
    (supp : Finset ℤ) (w : ℤ → ℝ) (M : ℝ)
    (hub : ∀ n ∈ supp, w n ≤ M) :
    firstMomentOf supp w ≤ (supp.card : ℝ) * M := by
  simpa [firstMomentOf] using
    Sieve.SumBounds.sum_le_card_mul_bound supp w M hub

/--
A fully abstracted bridge: whenever you can **represent** your `firstMoment W`
as `∑ n ∈ supp W, w W n` and you have a pointwise bound on that support,
you immediately get `firstMoment W ≤ (supp W).card * M W`.

Use this without depending on the concrete fields of your `Weight`.
-/
lemma firstMoment_le_card_mul_bound_of_repr
    {W : Type*}
    (firstMoment : W → ℝ)
    (supp       : W → Finset ℤ)
    (w          : W → ℤ → ℝ)
    (M          : W → ℝ)
    (repr : ∀ (W₀ : W), firstMoment W₀ = ∑ n ∈ supp W₀, w W₀ n)
    (hub  : ∀ (W₀ : W) n, n ∈ supp W₀ → w W₀ n ≤ M W₀) :
    ∀ (W₀ : W), firstMoment W₀ ≤ (supp W₀).card * M W₀ := by
  intro W₀
  have := Sieve.SumBounds.sum_le_card_mul_bound (supp W₀) (w W₀) (M W₀)
              (by intro n hn; exact hub W₀ n hn)
  simpa [repr W₀] using this

end Sieve.MomentBounds
