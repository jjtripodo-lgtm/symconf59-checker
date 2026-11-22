import Symconf59.ProfileMarkedCheck

namespace Symconf59

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checkPair_23_9 : pairKeyCoverage 23 9=true :=
  pair_with_marks 23 9 "XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX" (by decide +kernel)
theorem checkPair_23_10 : pairKeyCoverage 23 10=true :=
  pair_with_marks 23 10 "XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX" (by decide +kernel)
theorem checkPair_23_11 : pairKeyCoverage 23 11=true :=
  pair_with_marks 23 11 "XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX" (by decide +kernel)
theorem checkPair_23_12 : pairKeyCoverage 23 12=true :=
  pair_with_marks 23 12 "XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX" (by decide +kernel)
theorem checkPair_23_13 : pairKeyCoverage 23 13=true :=
  pair_with_marks 23 13 "XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX" (by decide +kernel)

end Symconf59
