import Mathlib
import MaynardTao.AdmissibleTuples
import MaynardTao.WeightsAPI
import MaynardTao.WeightOps
import MaynardTao.WeightOps2
import MaynardTao.Normalize
import MaynardTao.Sums
import MaynardTao.ShiftPrimes
import MaynardTao.PrimeCounts
import MaynardTao.SquareWeights
import MaynardTao.SelbergWeights
import MaynardTao.SelbergNormalized
import MaynardTao.Inequalities
import MaynardTao.Sandwich
import MaynardTao.Bridging
import MaynardTao.BridgingDemo
import MaynardTao.SelbergDemo
import MaynardTao.Criterion
import MaynardTao.Monotonicity
import MaynardTao.NumericsAPI
import MaynardTao.NumericsDemo
import MaynardTao.Admissible
import MaynardTao.AdmissibleLemmas
import MaynardTao.BoundedGaps
import MaynardTao.Params
import MaynardTao.Scenarios
import MaynardTao.WeightBuilders
import MaynardTao.NumericalVerification
import MaynardTao.Demo

/-!
# MaynardTao

Aggregator module: importing this brings the lightweight, sorry-free
Maynard–Tao scaffold into scope (admissible tuples + admissibility predicate/lemmas,
weights API, ops, normalization, sums, shifted primes, prime counts,
inequalities, sandwich/bridging, criterion, monotonicity, numerics API + demo,
square/selberg weights (incl. normalized), scenarios, and demos).
-/

namespace MaynardTao
-- Re-export key namespaces for convenience.
open BoundedGaps
open SieveWeight
end MaynardTao

import MaynardTao.AdmissibleTransforms
