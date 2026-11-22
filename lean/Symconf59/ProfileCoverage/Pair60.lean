import Symconf59.ProfileMarkedCheck

namespace Symconf59

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checkPair_26_14 : pairKeyCoverage 26 14=true :=
  pair_with_marks 26 14 "[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[OO[" (by decide +kernel)
theorem checkPair_26_15 : pairKeyCoverage 26 15=true :=
  pair_with_marks 26 15 "[[[[[[[[[[[[[[[[[[[[[[[[[[[[[N[[" (by decide +kernel)
theorem checkPair_26_16 : pairKeyCoverage 26 16=true :=
  pair_with_marks 26 16 "[[[[[[[[[[[[[[[[[[[[[[N[" (by decide +kernel)
theorem checkPair_26_17 : pairKeyCoverage 26 17=true :=
  pair_with_marks 26 17 "[[[[[[[[[[[[[[[[[[[R[" (by decide +kernel)
theorem checkPair_26_18 : pairKeyCoverage 26 18=true :=
  pair_with_marks 26 18 "[[[[[[[[[[[[[[[[[" (by decide +kernel)
theorem checkPair_26_19 : pairKeyCoverage 26 19=true :=
  pair_with_marks 26 19 "[[[[[[[[[[[[[" (by decide +kernel)
theorem checkPair_26_20 : pairKeyCoverage 26 20=true :=
  pair_with_marks 26 20 "[[[[[[[[[U" (by decide +kernel)
theorem checkPair_26_21 : pairKeyCoverage 26 21=true :=
  pair_with_marks 26 21 "[[[[[[[[[" (by decide +kernel)
theorem checkPair_26_22 : pairKeyCoverage 26 22=true :=
  pair_with_marks 26 22 "[[[[[[" (by decide +kernel)
theorem checkPair_26_23 : pairKeyCoverage 26 23=true :=
  pair_with_marks 26 23 "XXXXX" (by decide +kernel)
theorem checkPair_26_24 : pairKeyCoverage 26 24=true :=
  pair_with_marks 26 24 "[[[Y" (by decide +kernel)
theorem checkPair_26_25 : pairKeyCoverage 26 25=true :=
  pair_with_marks 26 25 "[[[" (by decide +kernel)
theorem checkPair_26_26 : pairKeyCoverage 26 26=true :=
  pair_with_marks 26 26 "DH" (by decide +kernel)

end Symconf59
