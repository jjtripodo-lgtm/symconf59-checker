module

public import Symconf59.UnrestrictedWithChecks
public import Symconf59.ProfileCheckedKeys

@[expose] public section

/-! Literal unrestricted symmetric configuration `(59_8)` nonexistence.
No parity constraint, common-profile assumption, or unverified arithmetic oracle. -/
namespace Symconf59

/-- No binary 59-by-59 incidence matrix with eight ones in each row and
column and at most one common one for every pair of distinct rows exists. -/
theorem no_symconf_59_8 (A : Int59) (hA : Incidence59 A) : False :=
  no_incidence_of_checked_profile_keys all_key_valid top_key_coverage_all A hA

theorem no_unrestricted_incidence59 : ¬ ∃ A : Int59, Incidence59 A :=
  fun ⟨A,hA⟩ => no_symconf_59_8 A hA

end Symconf59
