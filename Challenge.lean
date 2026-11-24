module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Nonexistence of a symmetric configuration 59_8
An incidence matrix on 59 points and 59 lines has binary entries, every
row and column sum is 8, and two distinct rows share at most one incidence.
There is no such matrix. No cyclicity or arithmetic premise is imposed.
The formalization accompanies the manuscript *There is no symmetric
configuration 59₈*, Hexagon 2611.00901v1.
-/

@[expose] public section
open scoped BigOperators
namespace PalomarSymconf

theorem no_configuration_59_8 :
    ¬ ∃ A : Matrix (Fin 59) (Fin 59) ℤ,
      (∀ i j, A i j = 0 ∨ A i j = 1) ∧
      (∀ i, (∑ j, A i j) = 8) ∧
      (∀ j, (∑ i, A i j) = 8) ∧
      (∀ i i', i ≠ i' → (∑ j, A i j * A i' j) ≤ 1) := by
  sorry

end PalomarSymconf
