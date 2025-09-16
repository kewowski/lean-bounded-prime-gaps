import Mathlib
import MaynardTao.AdmissibleTuples
import MaynardTao.WeightsAPI

/-!
MaynardTao/Params.lean
----------------------
Helpers for `WeightParams`:

* `mkParams H hAdm` : coherent constructor with `k = H.card`.
* `coherent P`      : predicate asserting `P.k = P.H.card`.
* `coherent_mkParams` : proof that `mkParams` is coherent.
-/

namespace MaynardTao

/-- Build coherent parameters from an admissible `H`, setting `k := H.card`. -/
def mkParams (H : Finset ℤ) (hAdm : isAdmissible H) : WeightParams :=
{ H := H, k := H.card, admissible := hAdm }

/-- `P` is coherent if its `k` matches `H.card`. -/
def coherent (P : WeightParams) : Prop := P.k = P.H.card

@[simp] lemma coherent_mkParams (H : Finset ℤ) (hAdm : isAdmissible H) :
    coherent (mkParams H hAdm) := rfl

end MaynardTao
