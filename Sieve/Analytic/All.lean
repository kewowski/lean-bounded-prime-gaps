/-
  Sieve/Analytic/All.lean
  One-line import hub for the lightweight analytic toolbox.

  Purpose:
  - Provide a stable, single import for downstream demos/tests.
  - Keep leaf modules decoupled from Stage-2/3 while remaining easy to use.

  Usage:
    import Sieve.Analytic.All
-/

-- Core toolbox
import Sieve.Analytic.LargeSieveCore

-- Small, focused helpers and wrappers
import Sieve.Analytic.ResidueIndicator
import Sieve.Analytic.ResidueSumBasics
import Sieve.Analytic.ResidueSumLinear
import Sieve.Analytic.SumSwapResidues
import Sieve.Analytic.IndexCounting
import Sieve.Analytic.PartialSummationConvenience
import Sieve.Analytic.PerModulusCSConvenience
import Sieve.Analytic.DataMassBasics

-- Trivial bounds (no large-sieve needed)
import Sieve.Analytic.ResidueMassTrivialBounds
import Sieve.Analytic.ResidueL1TrivialBounds
import Sieve.Analytic.WeightedResidueL1TrivialBounds

-- Weighted-by-n helpers
import Sieve.Analytic.WeightedResidue
import Sieve.Analytic.WeightedResidueConst

-- Large-sieve convenience layers
import Sieve.Analytic.LargeSieveConvenience
import Sieve.Analytic.LargeSieveWeightedConvenience
import Sieve.Analytic.LargeSieveDefs
import Sieve.Analytic.LargeSieveMassDyadic
import Sieve.Analytic.LargeSieveMonotonicity

-- Cauchy–Schwarz packaging (L¹ from L²)
import Sieve.Analytic.L1FromCS
import Sieve.Analytic.L1IccConvenience
import Sieve.Analytic.L1DyadicConvenience
import Sieve.Analytic.L1WeightedIccConvenience
import Sieve.Analytic.L1Monotonicity
import Sieve.Analytic.L1NMonotonicity
import Sieve.Analytic.L1ConstWeightConvenience

-- Params with epsilon-loss and constants ledger
import Sieve.Analytic.BVSketchParamsEps
import Sieve.Analytic.BVConstantsLedger

-- Tiny smoke wrappers
import Sieve.Analytic.RunLargeSieveSmoke
import Sieve.Analytic.RunDyadicSmoke
import Sieve.Analytic.RunOrthogonalitySmoke
import Sieve.Analytic.RunPartialSummationSmoke
import Sieve.Analytic.RunConstWeightSmoke
