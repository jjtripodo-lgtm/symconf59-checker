module

public import Symconf59.ProfileMarkedCheck

@[expose] public section

namespace Symconf59

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checkPair_19_5 : pairKeyCoverage 19 5=true :=
  pair_with_marks 19 5 "TTTTTTTTTTTTTT" (by decide +kernel)
theorem checkPair_19_6 : pairKeyCoverage 19 6=true :=
  pair_with_marks 19 6 "TTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTT" (by decide +kernel)
theorem checkPair_19_7 : pairKeyCoverage 19 7=true :=
  pair_with_marks 19 7 "TTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTT" (by decide +kernel)
theorem checkPair_19_8 : pairKeyCoverage 19 8=true :=
  pair_with_marks 19 8 "TTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTT" (by decide +kernel)
theorem checkPair_19_9 : pairKeyCoverage 19 9=true :=
  pair_with_marks 19 9 "TTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTT" (by decide +kernel)

end Symconf59
