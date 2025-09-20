/-
  Sieve/PipelineSimp.lean
  Small simp lemmas exposing stage1 hits = MT moments (by definition).
-/
import Mathlib
import Sieve.Pipeline
import Sieve.MTMoments

noncomputable section
open Classical

namespace Sieve.Pipeline

@[simp] lemma stage1_hits_first (cfg : Config) (W : Sieve.MaynardWeights.Weight) :
    (stage1 cfg W).hits.firstMomentLower = Sieve.MTMoments.firstMoment W := rfl

@[simp] lemma stage1_hits_second (cfg : Config) (W : Sieve.MaynardWeights.Weight) :
    (stage1 cfg W).hits.secondMomentUpper = Sieve.MTMoments.secondMoment W := rfl

end Sieve.Pipeline
