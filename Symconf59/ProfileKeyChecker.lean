module

public import Symconf59.ProfileBadKeys

@[expose] public section

/-! Separate validation of each small numerical countercertificate and
coverage for every literal descending partition. -/
namespace Symconf59

def bucket (a : ℕ) : List (List ℕ) := badKeys59[a]?.getD []

def keyValid (a : ℕ) : Bool :=
  (bucket a).all (fun K => !(rowPossible a K 8 (a+5)))

def keyObstruction (P : List ℕ) (a : ℕ) : Bool :=
  (bucket a).contains (P.filter (relevant a))

def topKeyCoverage (a : ℕ) : Bool :=
  (afterFirst a).all (fun P => locallyAllowed.contains P || P.any (keyObstruction P))

/-- Only lemma inputs are the two explicit, bounded checks. Correctness
covers every original positive descending profile, with no parity
hypothesis and no guarantee of certification assumed for a true row. -/
theorem five_profiles_from_key_certs
    (hV : ∀ a : Fin 60, keyValid a.val=true)
    (hCov : ∀ a : Fin 60, 3≤a.val → topKeyCoverage a.val=true)
    (P : List ℕ) (hSum : P.sum=59) (hMin : ∀ a∈P,3≤a)
    (hSort : P.Pairwise (· ≥ ·))
    (h : ∀ a∈P, LocalRowBudget a P 8 (a+5)) : P∈locallyAllowed := by
  obtain ⟨top,ht,hp⟩ := original_afterFirst P hSum hMin hSort
  have hh := List.all_eq_true.mp (hCov top ht) P hp
  rw [Bool.or_eq_true] at hh
  rcases hh with hgood | hbad
  · exact List.contains_iff_mem.mp hgood
  · exfalso
    obtain ⟨a,ha,hkey⟩ := List.any_eq_true.mp hbad
    have ha' : a≤59 := hSum ▸ member_le_sum ha
    let i : Fin 60 := ⟨a,by omega⟩
    have hk : P.filter (relevant a) ∈ bucket a := List.contains_iff_mem.mp hkey
    have hv := hV i
    change (bucket a).all (fun K => !(rowPossible a K 8 (a+5)))=true at hv
    have hn : (!(rowPossible a (P.filter (relevant a)) 8 (a+5)))=true :=
      List.all_eq_true.mp hv _ hk
    have hp : 0<a := by have := hMin a ha; omega
    have ht := rowPossible_complete (localRow_filter_relevant hp (h a ha))
    rw [ht] at hn
    exact Bool.false_ne_true hn

end Symconf59
