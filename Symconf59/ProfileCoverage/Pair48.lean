module

public import Symconf59.ProfileMarkedCheck

@[expose] public section

namespace Symconf59

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checkPair_20_19 : pairKeyCoverage 20 19=true :=
  pair_with_marks 20 19 "TTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTR" (by decide +kernel)
theorem checkPair_20_20 : pairKeyCoverage 20 20=true :=
  pair_with_marks 20 20 "EDDDEEGDDHHHHHHDIIHDJJJHDEDJLLLDHNNOPQT" (by decide +kernel)
theorem checkPair_21_3 : pairKeyCoverage 21 3=true :=
  pair_with_marks 21 3 "" (by decide +kernel)
theorem checkPair_21_4 : pairKeyCoverage 21 4=true :=
  pair_with_marks 21 4 "EEV" (by decide +kernel)
theorem checkPair_21_5 : pairKeyCoverage 21 5=true :=
  pair_with_marks 21 5 "FFFEFVEVFVEVV" (by decide +kernel)
theorem checkPair_21_6 : pairKeyCoverage 21 6=true :=
  pair_with_marks 21 6 "EGVFFFEFEFVEEVFFEVVVEVFFEVEFVVF" (by decide +kernel)
theorem checkPair_21_7 : pairKeyCoverage 21 7=true :=
  pair_with_marks 21 7 "EHHFFHHEHHHEHFFHHEGEHFHEEFHEHHHFFFHEHHFGGHGFHHEFFEGFFEFGA" (by decide +kernel)
theorem checkPair_21_8 : pairKeyCoverage 21 8=true :=
  pair_with_marks 21 8 "IIVFFFVIVIVIIVFFFIVIVFVIIVFIVHHFFHHIHFFHHFFIHFIIIIIFIIVFFVVIVFFVVVHHFHHFHHFVFVVFHHVV" (by decide +kernel)
theorem checkPair_21_9 : pairKeyCoverage 21 9=true :=
  pair_with_marks 21 9 "EJFFVEVEJVEVFFEVVEFVEVFVEHFHJEEJFHEJJHJFJHJJJFIJFVVIIVFVIVIHFJJFJJIVVVHJVEVFFEVEFVVFEFHEHGIVFIVFVVFVEI" (by decide +kernel)

end Symconf59
