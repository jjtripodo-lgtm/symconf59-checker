module

public import Symconf59.Unrestricted59

@[expose] public section
open scoped BigOperators
namespace PalomarSymconf

theorem no_configuration_59_8 :
    ¬ ∃ A : Matrix (Fin 59) (Fin 59) ℤ,
      (∀ i j, A i j = 0 ∨ A i j = 1) ∧
      (∀ i, (∑ j, A i j) = 8) ∧
      (∀ j, (∑ i, A i j) = 8) ∧
      (∀ i i', i ≠ i' → (∑ j, A i j * A i' j) ≤ 1) := by
  rintro ⟨A, hb, hr, hc, ho⟩
  exact Symconf59.no_unrestricted_incidence59 ⟨A, ⟨hb, hr, hc, ho⟩⟩

end PalomarSymconf
