/-
  Sieve/Stage2.lean
  Minimal Stage 2 scaffold + a generic first-moment bound lemma
  that only assumes a representation as a finite sum and a pointwise bound.
-/
import Mathlib
import Sieve.Pipeline
import Sieve.GallagherHook
import Sieve.AdmissibleTwin
import Sieve.MomentBounds

noncomputable section
open Classical

namespace Sieve.Stage2

/-- Output of Stage 2: currently just the Gallagher `B` and its nonnegativity. -/
structure Result where
  B      : ℝ
  nonneg : 0 ≤ B

/-- Generic Stage 2 runner for any config. -/
def run (cfg : Sieve.Pipeline.Config) : Result :=
  ⟨cfg.contract.gallagher.B, cfg.contract.gallagher.nonneg⟩

/-- Convenience: Stage 2 specialized to the twin configuration `{0,2}`. -/
def runTwin : Result :=
  run Sieve.AdmissibleTwin.twinConfig

/-- Trivial but useful inequality that always holds in Stage 2. -/
lemma B_nonneg (cfg : Sieve.Pipeline.Config) : 0 ≤ (run cfg).B :=
  (run cfg).nonneg

/-- Specialized version for the twin tuple. -/
lemma twin_B_nonneg : 0 ≤ (runTwin).B :=
  (runTwin).nonneg

/-
  NEW: A fully generic first-moment bound you can apply as soon as you
  have (1) a representation of `firstMoment` as a sum over a finite support
  and (2) a pointwise upper bound on that support.
-/
/-- If `firstMoment W = ∑ n ∈ supp W, w W n` and `w W n ≤ M W` on `supp W`,
then `firstMoment W ≤ (supp W).card * M W`. -/
lemma firstMoment_bound_of_repr
    {W : Type*}
    (firstMoment : W → ℝ)
    (supp       : W → Finset ℤ)
    (w          : W → ℤ → ℝ)
    (M          : W → ℝ)
    (repr : ∀ (W₀ : W), firstMoment W₀ = ∑ n ∈ supp W₀, w W₀ n)
    (hub  : ∀ (W₀ : W) n, n ∈ supp W₀ → w W₀ n ≤ M W₀)
    (W₀ : W) :
    firstMoment W₀ ≤ (supp W₀).card * M W₀ := by
  exact Sieve.MomentBounds.firstMoment_le_card_mul_bound_of_repr
    (firstMoment := firstMoment) (supp := supp) (w := w) (M := M)
    (repr := repr) (hub := hub) W₀

end Sieve.Stage2
