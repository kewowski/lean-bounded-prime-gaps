/-
  Sieve/Stage3Window.lean
  Generic "window sum" + average ≥⇒ max witness, plus a heavy-set specialization.
-/
import Mathlib
import Sieve.MTCore

noncomputable section
open Classical BigOperators

namespace Sieve
namespace Stage3

/-- Window sum across shifts `H`: `n ↦ ∑_{h∈H} f(n+h)`. -/
def windowSum (H : Finset ℤ) (f : ℤ → ℝ) (n : ℤ) : ℝ :=
  ∑ h ∈ H, f (n + h)

/-- Average of `g` over a finite set `A`. -/
def avgOver (A : Finset ℤ) (g : ℤ → ℝ) : ℝ :=
  (∑ n ∈ A, g n) / (A.card : ℝ)

/-- General "exists point ≥ average" for any finite nonempty set and function. -/
theorem exists_ge_avg_over
    {α} [DecidableEq α] (A : Finset α) (f : α → ℝ) (hA : A.Nonempty) :
    ∃ x ∈ A, (∑ a ∈ A, f a) / (A.card : ℝ) ≤ f x := by
  classical
  -- pick maximizer of f on A
  obtain ⟨x, hx, hmax⟩ := Finset.exists_max_image A f hA
  -- sum ≤ card * max
  have hsum_le : (∑ a ∈ A, f a) ≤ (A.card : ℝ) * f x := by
    have : ∑ a ∈ A, f a ≤ ∑ _a ∈ A, f x :=
      Finset.sum_le_sum (by intro a ha; exact hmax a ha)
    simpa [Finset.sum_const, nsmul_eq_mul, mul_comm] using this
  -- divide by |A| > 0
  have hpos : 0 < (A.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hA
  have hdiv :
      (∑ a ∈ A, f a) / (A.card : ℝ) ≤ ((A.card : ℝ) * f x) / (A.card : ℝ) :=
    div_le_div_of_nonneg_right hsum_le (le_of_lt hpos)
  -- simplify RHS to f x via mul_div_assoc + div_self
  have hne : (A.card : ℝ) ≠ 0 := ne_of_gt hpos
  have rhs_eq :
      ((A.card : ℝ) * f x) / (A.card : ℝ) = f x := by
    calc
      ((A.card : ℝ) * f x) / (A.card : ℝ)
          = (f x * (A.card : ℝ)) / (A.card : ℝ) := by simp [mul_comm]
      _ = f x * ((A.card : ℝ) / (A.card : ℝ)) := by simp [mul_div_assoc]
      _ = f x := by simp [div_self hne]
  have : (∑ a ∈ A, f a) / (A.card : ℝ) ≤ f x := by simpa [rhs_eq] using hdiv
  exact ⟨x, hx, this⟩

/-- Specialization: within the heavy set, some point attains at least the
average window sum. -/
theorem exists_heavy_with_window_ge_avg
    (W : Sieve.MaynardWeights.Weight) (τ : ℝ)
    (H : Finset ℤ) (f : ℤ → ℝ)
    (hne : (Sieve.MTCore.heavySet W τ).Nonempty) :
    ∃ n ∈ Sieve.MTCore.heavySet W τ,
      avgOver (Sieve.MTCore.heavySet W τ) (windowSum H f)
        ≤ windowSum H f n := by
  classical
  set A : Finset ℤ := Sieve.MTCore.heavySet W τ
  -- apply the general lemma with α = ℤ and g = windowSum H f
  simpa [A, avgOver, windowSum] using
    exists_ge_avg_over (A := A) (f := fun n => windowSum H f n) hne

end Stage3
end Sieve


