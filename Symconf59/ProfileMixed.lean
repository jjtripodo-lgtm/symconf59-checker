module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith

@[expose] public section

/-! Exact mixed profile exclusions from the first, second and cross
moments. The stronger target does not even need periodicity. -/
namespace Symconf59
open scoped BigOperators

/-- Two weighted moments and exact integer block total conversion. -/
structure ProfileRow {ι : Type*} [Fintype ι] (L : ι → ℕ) (a : ℕ) where
  u : ι → ℕ
  v : ι → ℕ
  block : ∀ j, a*u j=L j*v j
  momentOne : (∑ j,L j*v j)=8*a
  momentTwo : (∑ j,L j*v j*v j)=a*(a+5)

def CrossMoment {ι : Type*} [Fintype ι] {L : ι → ℕ} {a b : ℕ}
    (r : ProfileRow L a) (s : ProfileRow L b) : Prop :=
  (∑ j,L j*r.v j*s.v j)=a*b

section Generic
variable {ι : Type*} [Fintype ι] {L : ι → ℕ} {a : ℕ}

private theorem entry_square_le (r : ProfileRow L a) (j : ι) :
    L j*r.v j*r.v j≤a*(a+5) := by
  classical
  rw [← r.momentTwo]
  exact Finset.single_le_sum (fun i _ => Nat.zero_le (L i*r.v i*r.v i)) (Finset.mem_univ j)

private theorem entry_bound_three_five (r : ProfileRow L 3) (j : ι) (hj : L j=5) : r.v j=0 := by
  have h := entry_square_le r j
  rw [hj] at h
  have hcap : r.v j<3 := by
    by_contra hh
    have ht : 3≤r.v j := by omega
    have hq := Nat.mul_le_mul (Nat.mul_le_mul_left 5 ht) ht
    omega
  have hc := r.block j
  rw [hj] at hc
  omega

private theorem entry_bound_five_three (r : ProfileRow L 5) (j : ι) (hj : L j=3) : r.v j=0 := by
  have h := entry_square_le r j
  rw [hj] at h
  have hcap : r.v j<5 := by
    by_contra hh
    have ht : 5≤r.v j := by omega
    have hq := Nat.mul_le_mul (Nat.mul_le_mul_left 3 ht) ht
    omega
  have hc := r.block j
  rw [hj] at hc
  omega

/-- Disjoint support of actual length-three and length-five rows whenever
all the column lengths are three or five. In particular excludes 3^8+5^7. -/
theorem mixed_3_5_cross_impossible (hL : ∀ j, L j=3 ∨ L j=5)
    (r : ProfileRow L 3) (s : ProfileRow L 5) : ¬CrossMoment r s := by
  have hzero : (∑ j,L j*r.v j*s.v j)=0 := by
    apply Finset.sum_eq_zero
    intro j _
    rcases hL j with h|h
    · rw [entry_bound_five_three s j h,mul_zero]
    · rw [entry_bound_three_five r j h,mul_zero,zero_mul]
  intro h
  unfold CrossMoment at h
  omega

private theorem three_entry_cap (r : ProfileRow L 3) (hL : ∀j, 0<L j) (j : ι) :
    r.v j≤1 := by
  classical
  have hle (i : ι) : L i*r.v i≤L i*r.v i*r.v i := by
    by_cases hi : r.v i=0
    · simp [hi]
    · simpa only [mul_one] using Nat.mul_le_mul_left (L i*r.v i) (show 1≤r.v i by omega)
  by_contra hh
  have hv : 1<r.v j := by omega
  have hp : 0<L j*r.v j := Nat.mul_pos (hL j) (by omega)
  have hs : L j*r.v j<L j*r.v j*r.v j := by
    simpa only [mul_one] using Nat.mul_lt_mul_of_pos_left hv hp
  have ht : (∑i,L i*r.v i)<∑i,L i*r.v i*r.v i :=
    Finset.sum_lt_sum (fun i _ => hle i) ⟨j,Finset.mem_univ j,hs⟩
  rw [r.momentOne,r.momentTwo] at ht
  omega

private theorem five_entry_cap_fifteen (r : ProfileRow L 5) (j : ι) (hL : L j=15) :
    r.v j≤1 := by
  have h := entry_square_le r j
  rw [hL] at h
  by_contra hh
  have ht : 2≤r.v j := by omega
  have hq := Nat.mul_le_mul (Nat.mul_le_mul_left 15 ht) ht
  omega

end Generic

/-- The actual ordered list of block lengths in the second mixed profile. -/
def mixedLengths : Fin 7 → ℕ :=
  fun i => if i.val<3 then 3 else if i.val=3 then 5 else 15

private theorem l0 : mixedLengths 0=3 := by decide
private theorem l1 : mixedLengths 1=3 := by decide
private theorem l2 : mixedLengths 2=3 := by decide
private theorem l3 : mixedLengths 3=5 := by decide
private theorem l4 : mixedLengths 4=15 := by decide
private theorem l5 : mixedLengths 5=15 := by decide
private theorem l6 : mixedLengths 6=15 := by decide
private theorem lpos : ∀ j : Fin 7, 0<mixedLengths j := by decide

private theorem sum7 (f : Fin 7 → ℕ) :
    (∑ j,f j)=f 0+f 1+f 2+f 3+f 4+f 5+f 6 := by
  simp [Fin.sum_univ_succ]
  ring

private theorem row3_shape (r : ProfileRow mixedLengths 3) :
    r.v 0=1 ∧ r.v 1=1 ∧ r.v 2=1 ∧ r.v 3=0 ∧ r.v 4+r.v 5+r.v 6=1 := by
  have h0 := three_entry_cap r lpos 0
  have h1 := three_entry_cap r lpos 1
  have h2 := three_entry_cap r lpos 2
  have h3 := entry_bound_three_five r 3 l3
  have h := r.momentOne
  rw [sum7,l0,l1,l2,l3,l4,l5,l6,h3] at h
  omega

private theorem binary_sq_nat (a : ℕ) (h : a≤1) : a*a=a := by
  have ht : a=0 ∨ a=1 := by omega
  rcases ht with rfl|rfl <;> decide

private theorem row5_shape (r : ProfileRow mixedLengths 5) :
    r.v 0=0 ∧ r.v 1=0 ∧ r.v 2=0 ∧ r.v 3=2 ∧ r.v 4+r.v 5+r.v 6=2 := by
  have h0 := entry_bound_five_three r 0 l0
  have h1 := entry_bound_five_three r 1 l1
  have h2 := entry_bound_five_three r 2 l2
  have h4 := binary_sq_nat _ (five_entry_cap_fifteen r 4 l4)
  have h5 := binary_sq_nat _ (five_entry_cap_fifteen r 5 l5)
  have h6 := binary_sq_nat _ (five_entry_cap_fifteen r 6 l6)
  have h := r.momentOne
  have hh := r.momentTwo
  rw [sum7,l0,l1,l2,l3,l4,l5,l6,h0,h1,h2] at h hh
  have he : r.v 3*r.v 3=r.v 3+2 := by nlinarith
  have hcap : r.v 3<3 := by
    by_contra hn
    have hge : 3≤r.v 3 := by omega
    have ht := Nat.mul_le_mul_left (r.v 3) hge
    nlinarith
  have hv : r.v 3=0 ∨ r.v 3=1 ∨ r.v 3=2 := by omega
  have good : r.v 3=2 := by
    rcases hv with hv|hv|hv
    · rw [hv] at he
      omega
    · rw [hv] at he
      omega
    · exact hv
  refine ⟨h0,h1,h2,good,?_⟩
  omega

private theorem disjoint_large (r s : ProfileRow mixedLengths 3) (h : CrossMoment r s) :
    r.v 4*s.v 4=0 ∧ r.v 5*s.v 5=0 ∧ r.v 6*s.v 6=0 := by
  obtain ⟨h0,h1,h2,h3,_⟩ := row3_shape r
  obtain ⟨k0,k1,k2,k3,_⟩ := row3_shape s
  unfold CrossMoment at h
  rw [sum7,l0,l1,l2,l3,l4,l5,l6,h0,h1,h2,h3,k0,k1,k2,k3] at h
  simp only [mul_one,mul_zero,add_zero] at h
  constructor
  · have ht : 15*(r.v 4*s.v 4)=0 := by
      have g : 15*r.v 4*s.v 4=0 := by omega
      simpa only [mul_assoc] using g
    omega
  · constructor
    · have ht : 15*(r.v 5*s.v 5)=0 := by
        have g : 15*r.v 5*s.v 5=0 := by omega
        simpa only [mul_assoc] using g
      omega
    · have ht : 15*(r.v 6*s.v 6)=0 := by
        have g : 15*r.v 6*s.v 6=0 := by omega
        simpa only [mul_assoc] using g
      omega

private theorem cross_large (r : ProfileRow mixedLengths 3) (s : ProfileRow mixedLengths 5)
    (h : CrossMoment r s) : r.v 4*s.v 4+r.v 5*s.v 5+r.v 6*s.v 6=1 := by
  obtain ⟨h0,h1,h2,h3,_⟩ := row3_shape r
  obtain ⟨k0,k1,k2,k3,_⟩ := row5_shape s
  unfold CrossMoment at h
  rw [sum7,l0,l1,l2,l3,l4,l5,l6,h0,h1,h2,h3,k0,k1,k2,k3] at h
  simp only [mul_one,mul_zero,zero_mul,add_zero,zero_add,mul_assoc] at h
  omega

private theorem occupancy_cap (a b c : ℕ) (ha : a≤1) (hb : b≤1) (hc : c≤1)
    (hab : a*b=0) (hac : a*c=0) (hbc : b*c=0) : a+b+c≤1 := by
  have ha' : a=0 ∨ a=1 := by omega
  have hb' : b=0 ∨ b=1 := by omega
  have hc' : c=0 ∨ c=1 := by omega
  rcases ha' with rfl|rfl <;> rcases hb' with rfl|rfl <;> rcases hc' with rfl|rfl
  all_goals simp_all

/-- The three row-3 cycles occupy distinct column-15 cycles; the row-5
cycle cannot intersect all three. Row-15 choices are immaterial. -/
theorem mixed_3_3_5_15_cross_impossible
    (a b c : ProfileRow mixedLengths 3) (s : ProfileRow mixedLengths 5)
    (hab : CrossMoment a b) (hac : CrossMoment a c) (hbc : CrossMoment b c)
    (has : CrossMoment a s) (hbs : CrossMoment b s) (hcs : CrossMoment c s) : False := by
  obtain ⟨hab4,hab5,hab6⟩ := disjoint_large a b hab
  obtain ⟨hac4,hac5,hac6⟩ := disjoint_large a c hac
  obtain ⟨hbc4,hbc5,hbc6⟩ := disjoint_large b c hbc
  have hcap (j : Fin 7) (u₁ : a.v j*b.v j=0) (u₂ : a.v j*c.v j=0) (u₃ : b.v j*c.v j=0) :
      (a.v j+b.v j+c.v j)*s.v j≤s.v j := by
    simpa only [one_mul] using Nat.mul_le_mul_right (s.v j)
      (occupancy_cap _ _ _ (three_entry_cap a lpos j) (three_entry_cap b lpos j)
        (three_entry_cap c lpos j) u₁ u₂ u₃)
  have h4 := hcap 4 hab4 hac4 hbc4
  have h5 := hcap 5 hab5 hac5 hbc5
  have h6 := hcap 6 hab6 hac6 hbc6
  simp only [add_mul] at h4 h5 h6
  have ha := cross_large a s has
  have hb := cross_large b s hbs
  have hc := cross_large c s hcs
  have hs := (row5_shape s).2.2.2.2
  omega

end Symconf59
