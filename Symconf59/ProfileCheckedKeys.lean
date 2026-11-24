module

public import Symconf59.ProfileCoverage.AllKeys
public import Symconf59.ProfileCoverage.Batch0
public import Symconf59.ProfileCoverage.Batch1
public import Symconf59.ProfileCoverage.Batch2
public import Symconf59.ProfileCoverage.Direct0
public import Symconf59.ProfileCoverage.Direct1
public import Symconf59.ProfileCoverage.Direct2
public import Symconf59.ProfileCoverage.Direct3
public import Symconf59.ProfileCoverage.Direct4
public import Symconf59.ProfileCoverage.Direct5
public import Symconf59.ProfileCoverage.Direct6
public import Symconf59.ProfileCoverage.TopBundle
public import Mathlib.Tactic.FinCases

@[expose] public section

namespace Symconf59

theorem top_key_coverage_all (a : Fin 60) (ha : 3≤a.val) : topKeyCoverage a.val=true := by
  fin_cases a
  · change 3≤0 at ha
    omega
  · change 3≤1 at ha
    omega
  · change 3≤2 at ha
    omega
  · exact keyCoverage3
  · exact keyCoverage4
  · exact keyCoverage5
  · exact keyCoverage6
  · exact keyCoverage7
  · exact keyCoverage8
  · exact keyCoverage9
  · exact keyCoverage10
  · exact keyCoverage11
  · exact keyCoverage12
  · exact keyCoverage13
  · exact keyCoverage14
  · exact keyCoverage15
  · exact keyCoverage16
  · exact keyCoverage17
  · exact keyCoverage18
  · exact keyCoverage19
  · exact keyCoverage20
  · exact keyCoverage21
  · exact keyCoverage22
  · exact keyCoverage23
  · exact keyCoverage24
  · exact keyCoverage25
  · exact keyCoverage26
  · exact keyCoverage27
  · exact keyCoverage28
  · exact keyCoverage29
  · exact keyCoverage30
  · exact keyCoverage31
  · exact keyCoverage32
  · exact keyCoverage33
  · exact keyCoverage34
  · exact keyCoverage35
  · exact keyCoverage36
  · exact keyCoverage37
  · exact keyCoverage38
  · exact keyCoverage39
  · exact keyCoverage40
  · exact keyCoverage41
  · exact keyCoverage42
  · exact keyCoverage43
  · exact keyCoverage44
  · exact keyCoverage45
  · exact keyCoverage46
  · exact keyCoverage47
  · exact keyCoverage48
  · exact keyCoverage49
  · exact keyCoverage50
  · exact keyCoverage51
  · exact keyCoverage52
  · exact keyCoverage53
  · exact keyCoverage54
  · exact keyCoverage55
  · exact keyCoverage56
  · exact keyCoverage57
  · exact keyCoverage58
  · exact keyCoverage59

/-- Exact parity-free coverage of all genuine local-budget profiles. -/
theorem five_profiles_59 (P : List ℕ) (hS : P.sum=59)
    (hMin : ∀a∈P,3≤a) (hSort : P.Pairwise (· ≥ ·))
    (hRows : ∀a∈P,LocalRowBudget a P 8 (a+5)) : P∈locallyAllowed :=
  five_profiles_from_key_certs all_key_valid top_key_coverage_all P hS hMin hSort hRows

end Symconf59
