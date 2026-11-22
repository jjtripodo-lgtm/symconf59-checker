import Symconf59.ProfileMarkedCheck

namespace Symconf59

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checkPair_25_18 : pairKeyCoverage 25 18=true :=
  pair_with_marks 25 18 "ZZZZZSZZSZZIZZZZZLZNZ" (by decide +kernel)
theorem checkPair_25_19 : pairKeyCoverage 25 19=true :=
  pair_with_marks 25 19 "TTTTTTTTTTTTTTTTT" (by decide +kernel)
theorem checkPair_25_20 : pairKeyCoverage 25 20=true :=
  pair_with_marks 25 20 "ZZEZZZZZZJZLZ" (by decide +kernel)
theorem checkPair_25_21 : pairKeyCoverage 25 21=true :=
  pair_with_marks 25 21 "ZVVZZZVVZV" (by decide +kernel)
theorem checkPair_25_22 : pairKeyCoverage 25 22=true :=
  pair_with_marks 25 22 "WWWWWWWWW" (by decide +kernel)
theorem checkPair_25_23 : pairKeyCoverage 25 23=true :=
  pair_with_marks 25 23 "XXXXXX" (by decide +kernel)
theorem checkPair_25_24 : pairKeyCoverage 25 24=true :=
  pair_with_marks 25 24 "ZYZZY" (by decide +kernel)
theorem checkPair_25_25 : pairKeyCoverage 25 25=true :=
  pair_with_marks 25 25 "ZEZJ" (by decide +kernel)
theorem checkPair_26_3 : pairKeyCoverage 26 3=true :=
  pair_with_marks 26 3 "[" (by decide +kernel)
theorem checkPair_26_4 : pairKeyCoverage 26 4=true :=
  pair_with_marks 26 4 "[[" (by decide +kernel)
theorem checkPair_26_5 : pairKeyCoverage 26 5=true :=
  pair_with_marks 26 5 "[[[[[[[[[[" (by decide +kernel)
theorem checkPair_26_6 : pairKeyCoverage 26 6=true :=
  pair_with_marks 26 6 "[[[[[[[[[[[[[[[[[[[[[[" (by decide +kernel)
theorem checkPair_26_7 : pairKeyCoverage 26 7=true :=
  pair_with_marks 26 7 "[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[" (by decide +kernel)
theorem checkPair_26_8 : pairKeyCoverage 26 8=true :=
  pair_with_marks 26 8 "[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[" (by decide +kernel)
theorem checkPair_26_9 : pairKeyCoverage 26 9=true :=
  pair_with_marks 26 9 "[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[" (by decide +kernel)
theorem checkPair_26_10 : pairKeyCoverage 26 10=true :=
  pair_with_marks 26 10 "[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[" (by decide +kernel)
theorem checkPair_26_11 : pairKeyCoverage 26 11=true :=
  pair_with_marks 26 11 "[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[" (by decide +kernel)
theorem checkPair_26_12 : pairKeyCoverage 26 12=true :=
  pair_with_marks 26 12 "[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[" (by decide +kernel)
theorem checkPair_26_13 : pairKeyCoverage 26 13=true :=
  pair_with_marks 26 13 "NNFFENNFGNFHHHHNGINFIIHNNFJHIKNKKNLLLLNFMDH" (by decide +kernel)

end Symconf59
