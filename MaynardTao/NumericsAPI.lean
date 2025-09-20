import Mathlib
import MaynardTao.SelbergNormalized
import MaynardTao.Inequalities
import MaynardTao.PrimeCounts
import MaynardTao.Sums
import MaynardTao.ShiftPrimes

/-!
MaynardTao/NumericsAPI.lean
---------------------------
Minimal API for running numerics:

* `Params`     : holds (N, r, θ, index set I, coefficients lam, shifts H).
* `weight`     : builds a normalized Selberg weight from (I, lam, N) (requires a positivity proof).
* `Assumption` : S_{≥ r} ≥ θ · S₀ formulated for the built weight.
* `Conclusion` : S' ≥ (r : ℚ) · θ · S₀ for the built weight.
* `criterion`  : Assumption ⇒ Conclusion (no Spec needed).
-/

namespace MaynardTao
namespace NumericsAPI

open scoped BigOperators

/-- User-facing numeric parameters. -/
structure Params where
  N   : ℕ
  r   : ℕ
  θ   : ℚ
  I   : Finset ℕ
  lam : ℕ → ℚ
  H   : Finset ℤ

variable {P : WeightParams}

/-- Normalized Selberg weight determined by `p` (requires positivity of the unnormalized total). -/
noncomputable def weight (p : Params)
    (hpos : 0 < (SelbergWeights.ofLamOnRange (P := P) p.I p.lam p.N).total)
    : SieveWeight P :=
  SelbergWeights.normalized (P := P) p.I p.lam p.N hpos

/-- The numerical assumption you verify externally: `S_{≥ r} ≥ θ · S₀` for the built weight. -/
def Assumption (p : Params)
    (hpos : 0 < (SelbergWeights.ofLamOnRange (P := P) p.I p.lam p.N).total) : Prop :=
  PrimeCounts.S_atLeast (W := weight (P := P) p hpos) p.N p.H p.r
    ≥ p.θ * Sums.S0 (W := weight (P := P) p hpos) p.N

/-- The desired conclusion for the built weight: `S' ≥ (r:ℚ) · θ · S₀`. -/
def Conclusion (p : Params)
    (hpos : 0 < (SelbergWeights.ofLamOnRange (P := P) p.I p.lam p.N).total) : Prop :=
  ShiftPrimes.S_prime (W := weight (P := P) p hpos) p.N p.H
    ≥ (p.r : ℚ) * p.θ * Sums.S0 (W := weight (P := P) p hpos) p.N

/-- Criterion (no Spec needed): if `Assumption` holds, then `Conclusion` follows. -/
theorem criterion (p : Params)
    (hpos : 0 < (SelbergWeights.ofLamOnRange (P := P) p.I p.lam p.N).total)
    (hθ : Assumption (P := P) p hpos) :
    Conclusion (P := P) p hpos := by
  classical
  -- base: S' ≥ (r : ℚ) * S_{≥ r}
  have base := Inequalities.RCrit_all
    (W := weight (P := P) p hpos) p.N p.H p.r
  -- flip to ≤ for chaining
  have baseLE :
      (p.r : ℚ) * PrimeCounts.S_atLeast (W := weight (P := P) p hpos) p.N p.H p.r
        ≤ ShiftPrimes.S_prime (W := weight (P := P) p hpos) p.N p.H := by
    simpa [Inequalities.RCrit, ge_iff_le] using base
  -- assumption as ≤
  have hθLE :
      p.θ * Sums.S0 (W := weight (P := P) p hpos) p.N
        ≤ PrimeCounts.S_atLeast (W := weight (P := P) p hpos) p.N p.H p.r := by
    simpa [ge_iff_le] using hθ
  -- multiply by (r : ℚ) ≥ 0
  have hr0 : 0 ≤ (p.r : ℚ) := by exact_mod_cast (Nat.zero_le p.r)
  have stepLE :
      (p.r : ℚ) * (p.θ * Sums.S0 (W := weight (P := P) p hpos) p.N)
        ≤ (p.r : ℚ) * PrimeCounts.S_atLeast (W := weight (P := P) p hpos) p.N p.H p.r :=
    mul_le_mul_of_nonneg_left hθLE hr0
  -- chain to get the final bound
  have boundLE :
      (p.r : ℚ) * (p.θ * Sums.S0 (W := weight (P := P) p hpos) p.N)
        ≤ ShiftPrimes.S_prime (W := weight (P := P) p hpos) p.N p.H :=
    le_trans stepLE baseLE
  -- present as ≥ with nicer association
  simpa [Conclusion, ge_iff_le, mul_left_comm, mul_assoc] using boundLE

end NumericsAPI
end MaynardTao
