import Symconf59.ProfilePairCheck

namespace Symconf59

/-- One witnessed answer to the original exact coverage predicate. A zero
does not waive verification: it directly checks membership in the known
short positive candidate list. -/
def markedProfileOK (P : List ℕ) (a : ℕ) : Bool :=
  if a=0 then locallyAllowed.contains P else P.contains a && keyObstruction P a

def markIndex (c : Char) : ℕ := c.toNat-65

def markedProfiles : List (List ℕ) → List Char → Bool
  | [],[] => true
  | P::Ps,c::cs => markedProfileOK P (markIndex c) && markedProfiles Ps cs
  | _,_ => false

theorem markedProfileOK_sound (P : List ℕ) (a : ℕ) (h : markedProfileOK P a=true) :
    (locallyAllowed.contains P || P.any (keyObstruction P))=true := by
  rw [Bool.or_eq_true]
  by_cases ha : a=0
  · left
    simpa only [markedProfileOK,if_pos ha] using h
  · right
    simp only [markedProfileOK,if_neg ha,Bool.and_eq_true] at h
    exact List.any_eq_true.mpr ⟨a,List.contains_iff_mem.mp h.1,h.2⟩

/-- Trust-free certificate use: each indexed hint is checked against the
original profile. Length mismatches fail, and hints never alter enumeration. -/
theorem markedProfiles_sound : ∀ (Ps : List (List ℕ)) (cs : List Char),
    markedProfiles Ps cs=true →
    Ps.all (fun P => locallyAllowed.contains P || P.any (keyObstruction P))=true
  | [],[],_ => rfl
  | _::_,[],h => False.elim (Bool.false_ne_true h)
  | [],_::_,h => False.elim (Bool.false_ne_true h)
  | P::Ps,c::cs,h => by
    simp only [markedProfiles,Bool.and_eq_true] at h
    simp only [List.all_cons,Bool.and_eq_true]
    exact ⟨markedProfileOK_sound _ _ h.1,markedProfiles_sound Ps cs h.2⟩

theorem pair_with_marks (a b : ℕ) (s : String)
    (h : markedProfiles (afterPair a b) s.toList=true) : pairKeyCoverage a b=true :=
  markedProfiles_sound _ _ h

end Symconf59
