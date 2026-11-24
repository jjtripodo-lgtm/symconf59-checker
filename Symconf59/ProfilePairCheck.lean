module

public import Symconf59.ProfileKeyChecker

@[expose] public section

namespace Symconf59

def afterPair (a b : ℕ) : List (List ℕ) :=
  (partitionLists 17 (59-a-b) b).map (fun P => a::b::P)

def pairKeyCoverage (a b : ℕ) : Bool :=
  (afterPair a b).all (fun P => locallyAllowed.contains P || P.any (keyObstruction P))

/-- Further exact reflection split: every actual second part comes from a
literal recursive partition branch. -/
theorem top_from_pair {a : ℕ} (ha : a<59)
    (h : ∀ b : Fin 60, 3≤b.val → b.val≤a → b.val≤59-a → pairKeyCoverage a b.val=true) :
    topKeyCoverage a=true := by
  apply List.all_eq_true.mpr
  intro P hP
  rw [afterFirst,List.mem_map] at hP
  obtain ⟨T,hT,rfl⟩ := hP
  simp only [partitionLists,show 59-a≠0 by omega,
    if_false,List.mem_flatMap,List.mem_filter,List.mem_range,List.mem_map,
    decide_eq_true_eq,Nat.lt_succ_iff,Nat.le_min] at hT
  obtain ⟨b,⟨⟨hb0,hb1⟩,hb2⟩,S,hS,rfl⟩ := hT
  have hcov := h ⟨b,by omega⟩ hb2 hb1 hb0
  apply List.all_eq_true.mp hcov
  exact List.mem_map.mpr ⟨S,hS,rfl⟩

end Symconf59
