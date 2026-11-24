module

public import Symconf59.ProfileMixed
public import Symconf59.ProfileCompact

@[expose] public section

/-! Symbolic matching of genuine cycle block sums and the finite checker. -/
namespace Symconf59
open scoped BigOperators

section Core
variable {ι : Type*} [Fintype ι] {L : ι → ℕ} {a : ℕ}

/-- Exact cancellation after converting weighted column sums to row sums. -/
theorem ProfileRow.normalized_moments (r : ProfileRow L a) (ha : 0<a) :
    (∑ j,r.u j)=8 ∧ (∑ j,r.u j*r.v j)=a+5 := by
  constructor
  · apply Nat.eq_of_mul_eq_mul_left ha
    rw [Finset.mul_sum, mul_comm a 8,← r.momentOne]
    exact Finset.sum_congr rfl (fun j _ => r.block j)
  · apply Nat.eq_of_mul_eq_mul_left ha
    rw [Finset.mul_sum,← r.momentTwo]
    apply Finset.sum_congr rfl
    intro j _
    rw [← mul_assoc,r.block]

/-- A proper shift counts the common selected support in exactly the
columns whose shared period divides it. -/
def ProfileRow.PeriodBounds (r : ProfileRow L a) : Prop :=
  ∀ d : ℕ, 0<d → d<a → (∑ j, if Nat.gcd a (L j)∣d then r.u j else 0)≤1

theorem ProfileRow.local_period_guard (r : ProfileRow L a) (ha : 0<a)
    (hP : r.PeriodBounds) (j : ι) : a∣L j ∨ r.u j≤1 := by
  classical
  by_cases hh : a∣L j
  · exact Or.inl hh
  right
  let g := Nat.gcd a (L j)
  have hG : g≤a := Nat.le_of_dvd ha (Nat.gcd_dvd_left _ _)
  have hne : g≠a := by
    intro he
    have hd : g∣L j := Nat.gcd_dvd_right _ _
    exact hh (he ▸ hd)
  have hp : 0<g := Nat.gcd_pos_of_pos_left _ ha
  have hsum := hP g hp (lt_of_le_of_ne hG hne)
  have hs : (if Nat.gcd a (L j)∣g then r.u j else 0) ≤
      (∑ i, if Nat.gcd a (L i)∣g then r.u i else 0) :=
    Finset.single_le_sum (f := fun i => if Nat.gcd a (L i)∣g then r.u i else 0)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  rw [if_pos (dvd_refl g)] at hs
  exact hs.trans hsum

end Core

private theorem indexedBudget (a : ℕ) (P : List ℕ) (u v : Fin P.length → ℕ)
    (hb : ∀j, 0<P.get j) (hu : ∀j,u j≤8) (hv : ∀j,v j≤8)
    (hdiv : ∀j,a*u j=(P.get j)*v j) (hloc : ∀j,a∣P.get j ∨ u j≤1) :
    LocalRowBudget a P (∑j,u j) (∑j,u j*v j) := by
  induction P with
  | nil =>
    simp only [List.length_nil,Finset.univ_eq_empty,Finset.sum_empty]
    exact LocalRowBudget.nil
  | cons b P ih =>
    let U : Fin P.length → ℕ := fun j => u j.succ
    let V : Fin P.length → ℕ := fun j => v j.succ
    have hh := ih U V (fun j => hb j.succ) (fun j => hu j.succ) (fun j => hv j.succ)
      (fun j => hdiv j.succ) (fun j => hloc j.succ)
    change LocalRowBudget a (b::P) (∑j : Fin (P.length+1),u j)
      (∑j : Fin (P.length+1),u j*v j)
    rw [Fin.sum_univ_succ,Fin.sum_univ_succ]
    exact
      LocalRowBudget.cons (a:=a) b P (u 0) (v 0) _ _ (hb 0) (hu 0) (hv 0)
        (hdiv 0) (hloc 0) hh

/-- The checker consumes the original length order, not a hand-selected
multiset of blocks. The positive row length and column capacities follow
from literal cycles and column incidence totals in the geometric application. -/
theorem ProfileRow.to_local_budget {P : List ℕ} {a : ℕ}
    (r : ProfileRow P.get a) (ha : 0<a) (hb : ∀j,0<P.get j)
    (hv : ∀j,r.v j≤8) (hper : r.PeriodBounds) :
    LocalRowBudget a P 8 (a+5) := by
  classical
  have hm := r.normalized_moments ha
  have hu (j : Fin P.length) : r.u j≤8 := by
    rw [← hm.1]
    exact Finset.single_le_sum (f := r.u)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  have hh := indexedBudget a P r.u r.v hb hu hv r.block (r.local_period_guard ha hper)
  rwa [hm.1,hm.2] at hh

end Symconf59
