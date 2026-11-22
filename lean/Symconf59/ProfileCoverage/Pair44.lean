import Symconf59.ProfileMarkedCheck

namespace Symconf59

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checkPair_19_15 : pairKeyCoverage 19 15=true :=
  pair_with_marks 19 15 "TTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTT" (by decide +kernel)
theorem checkPair_19_16 : pairKeyCoverage 19 16=true :=
  pair_with_marks 19 16 "TTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTT" (by decide +kernel)
theorem checkPair_19_17 : pairKeyCoverage 19 17=true :=
  pair_with_marks 19 17 "RRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRTT" (by decide +kernel)
theorem checkPair_19_18 : pairKeyCoverage 19 18=true :=
  pair_with_marks 19 18 "TTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTRT" (by decide +kernel)
theorem checkPair_19_19 : pairKeyCoverage 19 19=true :=
  pair_with_marks 19 19 "TTFFDTTTFGTFTHHHHHDTTFITHHFTJFTJHJTKTGKKLLLLLTFTMNNNOTTPQRT" (by decide +kernel)
theorem checkPair_20_3 : pairKeyCoverage 20 3=true :=
  pair_with_marks 20 3 "U" (by decide +kernel)
theorem checkPair_20_4 : pairKeyCoverage 20 4=true :=
  pair_with_marks 20 4 "UDD" (by decide +kernel)
theorem checkPair_20_5 : pairKeyCoverage 20 5=true :=
  pair_with_marks 20 5 "FFFFFUDEEDDDE" (by decide +kernel)

end Symconf59
