/- Sieve/RunAllSmoke.lean -/
import Sieve.AllExports

noncomputable section
open Classical

#check Sieve.Stage3.heavyDensity_le_one
#check Sieve.Stage3.exists_prime_in_window_of_AI_ge_one_from_avg
#check Sieve.Stage2.heavy_count_le_of_secondMoment
#check Sieve.AnalyticInputs.avgAsLower
