import Symconf59.ProfileArithmetic

/-! The two extra profiles left by the purely local test are excluded
by the exact aggregated proper shifts. Neither requires a parity gate. -/
namespace Symconf59
open scoped BigOperators

def penalty (a d b u : ℕ) : ℕ := if Nat.gcd a b∣d then u else 0

inductive ShiftRowBudget (a d e : ℕ) : List ℕ → ℕ → ℕ → ℕ → ℕ → Prop where
  | nil : ShiftRowBudget a d e [] 0 0 0 0
  | cons (b : ℕ) (P : List ℕ) (u v s q sD sE : ℕ) :
    0<b → u≤8 → v≤8 → a*u=b*v → (a∣b ∨ u≤1) →
    ShiftRowBudget a d e P s q sD sE →
    ShiftRowBudget a d e (b::P) (u+s) (u*v+q)
      (penalty a d b u+sD) (penalty a e b u+sE)

def guardedRowPossible (a d e : ℕ) (P : List ℕ) (s q sD sE : ℕ) : Bool :=
  match P with
  | [] => decide (s=0 ∧ q=0)
  | b::P => (List.range (min s 8+1)).any (fun u =>
      let v := a*u/b
      let pD := penalty a d b u
      let pE := penalty a e b u
      decide (0<b ∧ a*u=b*v ∧ v≤8 ∧ u*v≤q ∧ (a∣b ∨ u≤1) ∧ pD≤sD ∧ pE≤sE) &&
        guardedRowPossible a d e P (s-u) (q-u*v) (sD-pD) (sE-pE))

theorem guardedRow_complete {a d e : ℕ} {P : List ℕ} {s q sD sE : ℕ}
    (h : ShiftRowBudget a d e P s q sD sE)
    (B D : ℕ) (hB : sD≤B) (hD : sE≤D) : guardedRowPossible a d e P s q B D=true := by
  induction h generalizing B D with
  | nil => rfl
  | cons b P u v s q sD sE hb hu hv hd hloc hx ih =>
    have he : a*u/b=v := by rw [hd,Nat.mul_div_cancel_left _ hb]
    rw [guardedRowPossible,List.any_eq_true]
    refine ⟨u,?_ ,?_⟩
    · rw [List.mem_range,Nat.lt_succ_iff,Nat.le_min]
      exact ⟨Nat.le_add_right _ _,hu⟩
    · simp only [he,Bool.and_eq_true,decide_eq_true_eq,Nat.add_sub_cancel_left]
      exact ⟨⟨hb,hd,hv,Nat.le_add_right _ _,hloc,by omega,by omega⟩,
        ih _ _ (by omega) (by omega)⟩

private theorem indexedShiftBudget (a d e : ℕ) (P : List ℕ) (u v : Fin P.length → ℕ)
    (hb : ∀j, 0<P.get j) (hu : ∀j,u j≤8) (hv : ∀j,v j≤8)
    (hdiv : ∀j,a*u j=(P.get j)*v j) (hloc : ∀j,a∣P.get j ∨ u j≤1) :
    ShiftRowBudget a d e P (∑j,u j) (∑j,u j*v j)
      (∑j,penalty a d (P.get j) (u j)) (∑j,penalty a e (P.get j) (u j)) := by
  induction P with
  | nil =>
    simp only [List.length_nil,Finset.univ_eq_empty,Finset.sum_empty]
    exact ShiftRowBudget.nil
  | cons b P ih =>
    let U : Fin P.length → ℕ := fun j => u j.succ
    let V : Fin P.length → ℕ := fun j => v j.succ
    have hh := ih U V (fun j => hb j.succ) (fun j => hu j.succ) (fun j => hv j.succ)
      (fun j => hdiv j.succ) (fun j => hloc j.succ)
    change ShiftRowBudget a d e (b::P) (∑j : Fin (P.length+1),u j)
      (∑j : Fin (P.length+1),u j*v j)
      (∑j : Fin (P.length+1),penalty a d ((b::P).get j) (u j))
      (∑j : Fin (P.length+1),penalty a e ((b::P).get j) (u j))
    rw [Fin.sum_univ_succ,Fin.sum_univ_succ,Fin.sum_univ_succ,Fin.sum_univ_succ]
    exact
      ShiftRowBudget.cons (a:=a) (d:=d) (e:=e) b P (u 0) (v 0) _ _ _ _ (hb 0) (hu 0) (hv 0)
        (hdiv 0) (hloc 0) hh

theorem guardedRealProfile {P : List ℕ} {a d e : ℕ} (r : ProfileRow P.get a)
    (ha : 0<a) (hb : ∀j,0<P.get j) (hv : ∀j,r.v j≤8)
    (h : r.PeriodBounds) (hd : 0<d) (hd' : d<a) (he : 0<e) (he' : e<a) :
    guardedRowPossible a d e P 8 (a+5) 1 1=true := by
  have hs := r.normalized_moments ha
  have hu (j : Fin P.length) : r.u j≤8 := by
    rw [← hs.1]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  have hh := indexedShiftBudget a d e P r.u r.v hb hu hv r.block (r.local_period_guard ha h)
  rw [hs.1,hs.2] at hh
  exact guardedRow_complete hh 1 1 (h d hd hd') (h e he he')

abbrev extra21 : List ℕ := [21,7,7,7,7,7,3]
abbrev extra15 : List ℕ := [15,15,5,5,5,5,3,3,3]

set_option maxRecDepth 30000 in
private theorem extra21_refuted : guardedRowPossible 21 7 7 extra21 8 26 1 1=false := by decide +kernel

set_option maxRecDepth 30000 in
private theorem extra15_refuted : guardedRowPossible 15 5 3 extra15 8 20 1 1=false := by decide +kernel

/-- Excludes the exact first extra under honest divisibility and proper
shift periodicity. -/
theorem extra21_period_impossible (r : ProfileRow extra21.get 21)
    (hv : ∀j,r.v j≤8) (h : r.PeriodBounds) : False := by
  have hh := guardedRealProfile r (by decide) (by decide) hv h
    (d:=7) (e:=7) (by decide) (by decide) (by decide) (by decide)
  rw [extra21_refuted] at hh
  contradiction

/-- Excludes the exact second extra under honest divisibility and proper
shift periodicity. -/
theorem extra15_period_impossible (r : ProfileRow extra15.get 15)
    (hv : ∀j,r.v j≤8) (h : r.PeriodBounds) : False := by
  have hh := guardedRealProfile r (by decide) (by decide) hv h
    (d:=5) (e:=3) (by decide) (by decide) (by decide) (by decide)
  rw [extra15_refuted] at hh
  contradiction

end Symconf59
