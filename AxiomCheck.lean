import ALCS
import Solution

/-! Axioms used by the formalized statements (`lake env lean AxiomCheck.lean`). -/

-- Main results (Comparator)
#print axioms PalomarALCS.zero_class
#print axioms PalomarALCS.continuousOn_Phi
-- Section 1
#print axioms C0Semigroup.continuousOn_orbit
#print axioms ALCS.continuousOn_Phi_of_ne_top
#print axioms ALCS.zero_class
#print axioms ALCS.continuousOn_Phi
-- Section 2
#print axioms ALCS.norm_Phi_mono
#print axioms Phillips.full
#print axioms Phillips.uniform
-- Section 3
#print axioms exists_system_norm_Phi_eq_one
#print axioms ExoticMean.exotic_mean
#print axioms ExoticMean.Counterexample.no_representation
