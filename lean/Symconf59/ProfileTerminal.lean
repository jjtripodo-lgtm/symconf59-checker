import Symconf59.ProfileExtra
import Symconf59.ProfileKeyChecker
import Mathlib.Data.Fin.Rev

/-! Original list-indexed source arithmetic through all five cases.
The remaining derivation is the cycle-layout and physical-moment bridge. -/
namespace Symconf59
open scoped BigOperators

structure OriginalProfileFacts (P : List ℕ) where
  total : P.sum=59
  positive : ∀ a∈P,3≤a
  ordered : P.Pairwise (· ≥ ·)
  row : ∀ i : Fin P.length, ProfileRow P.get (P.get i)
  cap : ∀ i j, (row i).v j≤8
  period : ∀ i, (row i).PeriodBounds
  cross : ∀ i j : Fin P.length, i≠j → CrossMoment (row i) (row j)

private def ProfileRow.relabel {ι ι' : Type*} [Fintype ι] [Fintype ι']
    {L : ι → ℕ} {a : ℕ} (r : ProfileRow L a) (e : ι' ≃ ι) :
    ProfileRow (L ∘ e) a where
  u := r.u ∘ e
  v := r.v ∘ e
  block j := r.block (e j)
  momentOne := by
    change (∑ j, (fun i => L i*r.v i) (e j)) = _
    exact (Equiv.sum_comp e (fun i => L i*r.v i)).trans r.momentOne
  momentTwo := by
    change (∑ j, (fun i => L i*r.v i*r.v i) (e j)) = _
    exact (Equiv.sum_comp e (fun i => L i*r.v i*r.v i)).trans r.momentTwo

private theorem cross_relabel {ι ι' : Type*} [Fintype ι] [Fintype ι']
    {L : ι → ℕ} {a b : ℕ} (r : ProfileRow L a) (s : ProfileRow L b)
    (e : ι' ≃ ι) (h : CrossMoment r s) : CrossMoment (r.relabel e) (s.relabel e) := by
  unfold CrossMoment at h ⊢
  change (∑ j, (fun i => L i*r.v i*s.v i) (e j))=a*b
  exact (Equiv.sum_comp e (fun i => L i*r.v i*s.v i)).trans h

private theorem cross_transport {ι : Type*} [Fintype ι] {L M : ι → ℕ} {a b : ℕ}
    (e : L=M) (r : ProfileRow L a) (s : ProfileRow L b) (h : CrossMoment r s) :
    CrossMoment (e ▸ r) (e ▸ s) := by
  subst M
  exact h

abbrev mixedA : List ℕ := [5,5,5,5,5,5,5,3,3,3,3,3,3,3,3]
abbrev mixedB : List ℕ := [15,15,15,5,3,3,3]

private theorem mixedA_excluded (H : OriginalProfileFacts mixedA) : False := by
  have hs : ∀ j : Fin mixedA.length, mixedA.get j=3 ∨ mixedA.get j=5 := by decide
  have hr : CrossMoment (H.row 7) (H.row 0) := H.cross 7 0 (by decide)
  exact mixed_3_5_cross_impossible hs (H.row 7) (H.row 0) hr

private theorem mixedB_excluded (H : OriginalProfileFacts mixedB) : False := by
  let e : Fin 7 ≃ Fin mixedB.length := Fin.revPerm
  have he : mixedB.get ∘ e=mixedLengths := by
    funext j
    fin_cases j <;> decide
  let cols (a : ℕ) (r : ProfileRow mixedB.get a) : ProfileRow mixedLengths a :=
    he ▸ r.relabel e
  have crosses (a b : ℕ) (r : ProfileRow mixedB.get a) (s : ProfileRow mixedB.get b)
      (h : CrossMoment r s) : CrossMoment (cols a r) (cols b s) := by
    change CrossMoment (he ▸ r.relabel e) (he ▸ s.relabel e)
    exact cross_transport he _ _ (cross_relabel r s e h)
  refine mixed_3_3_5_15_cross_impossible (cols 3 (H.row 4)) (cols 3 (H.row 5)) (cols 3 (H.row 6))
    (cols 5 (H.row 3)) ?_ ?_ ?_ ?_ ?_ ?_
  · exact crosses 3 3 (H.row 4) (H.row 5) (H.cross 4 5 (by decide))
  · exact crosses 3 3 (H.row 4) (H.row 6) (H.cross 4 6 (by decide))
  · exact crosses 3 3 (H.row 5) (H.row 6) (H.cross 5 6 (by decide))
  · exact crosses 3 5 (H.row 4) (H.row 3) (H.cross 4 3 (by decide))
  · exact crosses 3 5 (H.row 5) (H.row 3) (H.cross 5 3 (by decide))
  · exact crosses 3 5 (H.row 6) (H.row 3) (H.cross 6 3 (by decide))

theorem singleton_of_true_arithmetic
    (hVal : ∀ a : Fin 60, keyValid a.val=true)
    (hCover : ∀ a : Fin 60, 3≤a.val → topKeyCoverage a.val=true)
    (P : List ℕ) (H : OriginalProfileFacts P) : P=[59] := by
  have hB : ∀ a∈P, LocalRowBudget a P 8 (a+5) := by
    intro a ha
    obtain ⟨i,hi⟩ := List.get_of_mem ha
    have h_pos : 0<P.get i := by
      have h := H.positive _ (List.get_mem P i)
      omega
    have hpos (j : Fin P.length) : 0<P.get j := by
      have h := H.positive _ (List.get_mem P j)
      omega
    rw [← hi]
    exact (H.row i).to_local_budget h_pos hpos (H.cap i) (H.period i)
  have hL := five_profiles_from_key_certs hVal hCover P H.total H.positive H.ordered hB
  change P∈[[59],extra21,mixedB,extra15,mixedA] at hL
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hL
  rcases hL with h|h|h|h|h
  · exact h
  · subst P
    exact (extra21_period_impossible (H.row 0) (H.cap 0) (H.period 0)).elim
  · subst P
    exact (mixedB_excluded H).elim
  · subst P
    exact (extra15_period_impossible (H.row 0) (H.cap 0) (H.period 0)).elim
  · subst P
    exact (mixedA_excluded H).elim

end Symconf59
