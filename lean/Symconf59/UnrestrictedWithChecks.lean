import Symconf59.OriginalCoordinates

/-! Analytical transport of the exact finite checks to literal unrestricted
incidence matrices. The two explicitly named finite checks are not assumed
as axioms; the final module proves both separately. -/
namespace Symconf59

private noncomputable def oneCycleChart : Site ≃ BlocksOf [59] :=
  Equiv.ofBijective (fun x => ⟨0,x⟩) (by
    constructor
    · intro x y h
      exact eq_of_heq (Sigma.mk.inj_iff.mp h).2
    · rintro ⟨i,x⟩
      have h : i=(0 : Fin ([59] : List ℕ).length) := by
        apply Fin.ext
        have hi := i.isLt
        change i.val<1 at hi
        change i.val=0
        omega
      subst i
      exact ⟨x,rfl⟩)

/-- No binary 59-by-59 incidence matrix with eight ones in each row and
column and at most one common one for every pair of distinct rows exists.
Both cycle decompositions and every arithmetic premise are derived from A. -/
theorem no_incidence_of_checked_profile_keys
    (hVal : ∀ a : Fin 60, keyValid a.val=true)
    (hCover : ∀ a : Fin 60, 3≤a.val → topKeyCoverage a.val=true)
    (A : Int59) (hA : Incidence59 A) : False := by
  obtain ⟨P,hs,hpos,horder,⟨R⟩,⟨C⟩⟩ := original_ordered_cycle_coords hA
  let G := physical_of_ordered_cycles hA hpos R C
  have facts := physical_blocks_to_profile hA G hs hpos horder
  have hsingle := singleton_of_true_arithmetic hVal hCover P facts
  subst P
  apply no_incidence_with_cyclic_row_leave (A:=A) (oneCycleChart.trans R.sites)
  intro i j
  exact R.same_block 0 i j

end Symconf59
