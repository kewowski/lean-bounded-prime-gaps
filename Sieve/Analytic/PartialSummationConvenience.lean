/-
  Sieve/Analytic/PartialSummationConvenience.lean
  Tiny telescoping identities for discrete differences (handy for partial
  summation / Abel summation steps).
-/
import Mathlib

noncomputable section
open Classical BigOperators

namespace Sieve
namespace Analytic

/--
Telescoping over a forward finite range (difference `h i - h (i+1)`):

  ∑_{i=0}^{N-1} (h i - h (i+1)) = h 0 - h N.
-/
theorem sum_range_telescope_sub_succ (h : ℕ → ℂ) :
    ∀ N, (∑ i ∈ Finset.range N, (h i - h (i+1))) = h 0 - h N := by
  intro N
  induction' N with N ih
  · simp
  · have hs :
        (∑ i ∈ Finset.range (N+1), (h i - h (i+1)))
          = (∑ i ∈ Finset.range N, (h i - h (i+1)))
              + (h N - h (N+1)) := by
        simpa using
          (Finset.sum_range_succ (f := fun i => (h i - h (i+1))) (n := N))
    calc
      (∑ i ∈ Finset.range (N+1), (h i - h (i+1)))
          = (∑ i ∈ Finset.range N, (h i - h (i+1)))
              + (h N - h (N+1)) := hs
      _ = (h 0 - h N) + (h N - h (N+1)) := by simp [ih]
      _ = h 0 - h (N+1) := by
            simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

/--
Variant with the difference in the other order:

  ∑_{i=0}^{N-1} (h (i+1) - h i) = h N - h 0.
-/
theorem sum_range_telescope_succ_sub (h : ℕ → ℂ) :
    ∀ N, (∑ i ∈ Finset.range N, (h (i+1) - h i)) = h N - h 0 := by
  intro N
  induction' N with N ih
  · simp
  · have hs :
        (∑ i ∈ Finset.range (N+1), (h (i+1) - h i))
          = (∑ i ∈ Finset.range N, (h (i+1) - h i))
              + (h (N+1) - h N) := by
        simpa using
          (Finset.sum_range_succ (f := fun i => (h (i+1) - h i)) (n := N))
    calc
      (∑ i ∈ Finset.range (N+1), (h (i+1) - h i))
          = (∑ i ∈ Finset.range N, (h (i+1) - h i))
              + (h (N+1) - h N) := hs
      _ = (h N - h 0) + (h (N+1) - h N) := by simp [ih]
      _ = h (N+1) - h 0 := by
            simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

end Analytic
end Sieve
