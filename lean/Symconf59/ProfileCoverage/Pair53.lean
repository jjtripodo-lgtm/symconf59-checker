import Symconf59.ProfileMarkedCheck

namespace Symconf59

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checkPair_22_16 : pairKeyCoverage 22 16=true :=
  pair_with_marks 22 16 "WWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWLQGQQWWWWWWWWWWWW" (by decide +kernel)
theorem checkPair_22_17 : pairKeyCoverage 22 17=true :=
  pair_with_marks 22 17 "RRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRW" (by decide +kernel)
theorem checkPair_22_18 : pairKeyCoverage 22 18=true :=
  pair_with_marks 22 18 "WWWWWWWWWWWWWWWWWWWWWWWWWWWWSFSWWWWWWW" (by decide +kernel)
theorem checkPair_22_19 : pairKeyCoverage 22 19=true :=
  pair_with_marks 22 19 "TTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTT" (by decide +kernel)
theorem checkPair_22_20 : pairKeyCoverage 22 20=true :=
  pair_with_marks 22 20 "WWWWWWWWWWWWWWWWWWWUUWWWR" (by decide +kernel)
theorem checkPair_22_21 : pairKeyCoverage 22 21=true :=
  pair_with_marks 22 21 "WVWWWVVWWWVWVWWWVVVWV" (by decide +kernel)
theorem checkPair_22_22 : pairKeyCoverage 22 22=true :=
  pair_with_marks 22 22 "WDFWWFWHHDHWJWEWP" (by decide +kernel)
theorem checkPair_23_3 : pairKeyCoverage 23 3=true :=
  pair_with_marks 23 3 "X" (by decide +kernel)
theorem checkPair_23_4 : pairKeyCoverage 23 4=true :=
  pair_with_marks 23 4 "XXX" (by decide +kernel)
theorem checkPair_23_5 : pairKeyCoverage 23 5=true :=
  pair_with_marks 23 5 "XXXXXXXXXXX" (by decide +kernel)
theorem checkPair_23_6 : pairKeyCoverage 23 6=true :=
  pair_with_marks 23 6 "XXXXXXXXXXXXXXXXXXXXXXXXXXXXX" (by decide +kernel)
theorem checkPair_23_7 : pairKeyCoverage 23 7=true :=
  pair_with_marks 23 7 "XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX" (by decide +kernel)
theorem checkPair_23_8 : pairKeyCoverage 23 8=true :=
  pair_with_marks 23 8 "XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX" (by decide +kernel)

end Symconf59
