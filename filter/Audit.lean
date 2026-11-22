import Dyadic
import Jump
import Linear
import Scale
import KernelTrunc
import Majorant
import Perron
import Orbit
import EdgeAssembly
import Conclusion

#print axioms RHFilter.pref_eq_odd_sub_half
#print axioms RHFilter.grid_eq_intervals
#print axioms RHFilter.grid_jump_valuation
#print axioms RHFilter.F_grid
#print axioms RHFilter.F_endpoint
#print axioms RHRealGrid.half_distance_lower
#print axioms RHFilter.Dyadic.finite_inverse
#print axioms RHFilter.inverse_F_with_endpoints
#print axioms RHFilter.Contour.source_hasSum_reciprocal
#print axioms RHFilter.F_lower_large_epsilon
#print axioms RHFilter.External.reciprocal_deriv_one
#print axioms RHFilter.External.reciprocal_holomorphic
#print axioms RHFilter.Trunc.near_half_log
#print axioms RHFilter.Majorant.vertical_arc_le
#print axioms RHFilter.Majorant.vertical_full_le
#print axioms RHFilter.Perron.edges_of_reciprocal_growth
#print axioms RHFilter.Perron.signed_shift
#print axioms RHFilter.Perron.local_budget
#print axioms RHFilter.Perron.minorant_of_analytic_steps
#print axioms RHFilter.minorant_from_truncation_and_growth

-- Display the hypotheses as well as the foundational axioms.
#check RHFilter.F_lower_large_epsilon
#check RHFilter.Perron.minorant_of_analytic_steps
#check RHFilter.minorant_from_truncation_and_growth
