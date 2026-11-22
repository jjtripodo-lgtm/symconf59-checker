import Symconf59.ProfileSieve

/-! Cheap parity-free arithmetic: every nonzero block occurs at a
comparably divisible column length, with ratio at most 8. -/
namespace Symconf59

def relevant (a b : ℕ) : Bool := decide ((a∣b ∧ b/a≤8) ∨ (b∣a ∧ a/b≤8))

private theorem relevant_of_positive {a b u v : ℕ} (ha : 0<a) (hb : 0<b)
    (hu0 : u≠0) (hu : u≤8) (hv : v≤8) (he : a*u=b*v)
    (hlocal : a∣b ∨ u≤1) : relevant a b=true := by
  apply decide_eq_true_eq.mpr
  rcases hlocal with ht|ht
  · left
    refine ⟨ht,?_⟩
    obtain ⟨c,hc⟩ := ht
    have hd : u=c*v := Nat.eq_of_mul_eq_mul_left ha (by rwa [hc,Nat.mul_assoc] at he)
    have hv1 : 1≤v := by
      by_contra hn
      have hz : v=0 := by omega
      rw [hz,mul_zero] at hd
      exact hu0 hd
    have hh := Nat.mul_le_mul_left c hv1
    rw [mul_one] at hh
    rw [hc,Nat.mul_div_cancel_left _ ha]
    omega
  · right
    have h1 : u=1 := by omega
    rw [h1,mul_one] at he
    exact ⟨⟨v,he⟩,by rw [he,Nat.mul_div_cancel_left _ hb]; exact hv⟩

/-- Dropping all impossible column lengths loses no true row witness. -/
theorem localRow_filter_relevant {a : ℕ} (ha : 0<a) {P : List ℕ} {s q : ℕ}
    (h : LocalRowBudget a P s q) : LocalRowBudget a (P.filter (relevant a)) s q := by
  induction h with
  | nil => exact LocalRowBudget.nil
  | cons b P u v s q hb hu hv he hloc htail ih =>
    by_cases hr : relevant a b=true
    · simp only [List.filter_cons,hr,if_true]
      exact LocalRowBudget.cons b _ u v s q hb hu hv he hloc ih
    · have hz : u=0 := by
        by_contra hn
        exact hr (relevant_of_positive ha hb hn hu hv he hloc)
      simp only [List.filter_cons,hr,hz,zero_mul,zero_add]
      exact ih

def compactRow (P : List ℕ) (a : ℕ) : Bool :=
  rowPossible a (P.filter (relevant a)) 8 (a+5)

def cheapRow (P : List ℕ) (a : ℕ) : Bool :=
  if (P.filter (relevant a)).length=1 then compactRow P a else true

/-- First fail cheaply on any singleton-supported row, then apply the actual
compact budget search. This intentionally uses no parity heuristic. -/
def compactProfile (P : List ℕ) : Bool :=
  P.all (cheapRow P) && P.all (compactRow P)

theorem compactProfile_complete (P : List ℕ) (hpos : ∀a∈P,0<a)
    (h : ∀a∈P, LocalRowBudget a P 8 (a+5)) : compactProfile P=true := by
  have hC (a : ℕ) (ha : a∈P) : compactRow P a=true :=
    rowPossible_complete (localRow_filter_relevant (hpos a ha) (h a ha))
  unfold compactProfile
  rw [Bool.and_eq_true,List.all_eq_true,List.all_eq_true]
  refine ⟨fun a ha => ?_,hC⟩
  unfold cheapRow
  split
  · exact hC a ha
  · rfl

def topCompactPass (a : ℕ) : Bool :=
  ((afterFirst a).filter compactProfile).all (fun p => locallyAllowed.contains p)

theorem five_profiles_of_compact_checks
    (hc : ∀ a : Fin 60, 3≤a.val → topCompactPass a.val=true)
    (P : List ℕ) (hSum : P.sum=59) (hMin : ∀ a∈P,3≤a)
    (hSort : P.Pairwise (· ≥ ·))
    (h : ∀ a∈P, LocalRowBudget a P 8 (a+5)) : P∈locallyAllowed := by
  obtain ⟨a,ha,hAp⟩ := original_afterFirst P hSum hMin hSort
  have ht : P∈(afterFirst a.val).filter compactProfile :=
    List.mem_filter.mpr ⟨hAp,compactProfile_complete P (fun a ha => by have := hMin a ha; omega) h⟩
  exact List.contains_iff_mem.mp (List.all_eq_true.mp (hc a ha) P ht)

end Symconf59
