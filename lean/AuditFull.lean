import Symconf59.Unrestricted59

open scoped BigOperators
#print axioms Symconf59.no_integral_gram_of_anisotropic_pair
#print axioms Symconf59.cycle59_no_integral_gram
#print axioms Symconf59.binary_simple_two_regular_leave
#print axioms Symconf59.cycleLayout_of_two_regular
#print axioms Symconf59.original_symmetric_step_trace_agrees
#print axioms Symconf59.original_match_cycle_components
#print axioms Symconf59.original_ordered_cycle_coords
#print axioms Symconf59.wave_binary_gcd_period
#print axioms Symconf59.cyclic_block_rows_constant
#print axioms Symconf59.physical_of_ordered_cycles
#print axioms Symconf59.physical_blocks_to_profile
#print axioms Symconf59.partitionLists_complete
#print axioms Symconf59.all_key_valid
#print axioms Symconf59.top_key_coverage_all
#print axioms Symconf59.five_profiles_59
#print axioms Symconf59.mixed_3_3_5_15_cross_impossible
#print axioms Symconf59.singleton_of_true_arithmetic
#print axioms Symconf59.no_symconf_59_8
#print axioms Symconf59.no_unrestricted_incidence59

example : ¬ ∃ A : Matrix (Fin 59) (Fin 59) ℤ, Symconf59.Incidence59 A :=
  Symconf59.no_unrestricted_incidence59

/-- Type-level readback: standard incidence conditions directly imply
False, with no (AA^mathsf{T}) or cycle premise. -/
example (A : Matrix (Fin 59) (Fin 59) ℤ)
    (h01 : ∀ i j, A i j = 0 ∨ A i j = 1)
    (hr : ∀ i, (∑ j, A i j) = 8) (hc : ∀ j, (∑ i, A i j) = 8)
    (ho : ∀ i j, i≠j → (∑ x, A i x*A j x)≤1) : False :=
  Symconf59.no_symconf_59_8 A ⟨h01,hr,hc,ho⟩
