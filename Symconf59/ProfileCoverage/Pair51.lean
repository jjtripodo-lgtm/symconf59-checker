module

public import Symconf59.ProfileMarkedCheck

@[expose] public section

namespace Symconf59

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checkPair_22_5 : pairKeyCoverage 22 5=true :=
  pair_with_marks 22 5 "WWWWWWWWWWWW" (by decide +kernel)
theorem checkPair_22_6 : pairKeyCoverage 22 6=true :=
  pair_with_marks 22 6 "WWWWWWWWWWWWWWWWWWWWWWWWWWWW" (by decide +kernel)
theorem checkPair_22_7 : pairKeyCoverage 22 7=true :=
  pair_with_marks 22 7 "WWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWW" (by decide +kernel)
theorem checkPair_22_8 : pairKeyCoverage 22 8=true :=
  pair_with_marks 22 8 "WWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWW" (by decide +kernel)
theorem checkPair_22_9 : pairKeyCoverage 22 9=true :=
  pair_with_marks 22 9 "WWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWW" (by decide +kernel)
theorem checkPair_22_10 : pairKeyCoverage 22 10=true :=
  pair_with_marks 22 10 "WWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWW" (by decide +kernel)

end Symconf59
