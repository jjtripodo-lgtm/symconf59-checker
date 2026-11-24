module

public import Symconf59.ProfileMarkedCheck

@[expose] public section

namespace Symconf59

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checkPair_22_11 : pairKeyCoverage 22 11=true :=
  pair_with_marks 22 11 "LLFFELDLLGFFEGLFELFHHHHHHHHHLLFLLFILFLIIGFIIHHHLLLGHLFJELFJHHHLIJILFIKKDLKGKKHKKIKKKLGWDFWWFWHHDHWJKE" (by decide +kernel)
theorem checkPair_22_12 : pairKeyCoverage 22 12=true :=
  pair_with_marks 22 12 "WWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWLFLLFHMIIMKMWWWWWWWWW" (by decide +kernel)
theorem checkPair_22_13 : pairKeyCoverage 22 13=true :=
  pair_with_marks 22 13 "WWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWNNNNNNNNNWWWWWWWWWWWWWWL" (by decide +kernel)
theorem checkPair_22_14 : pairKeyCoverage 22 14=true :=
  pair_with_marks 22 14 "WWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWOOOOOFOOWWWWWOWWWWWWWWW" (by decide +kernel)
theorem checkPair_22_15 : pairKeyCoverage 22 15=true :=
  pair_with_marks 22 15 "WWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWLLGPIPWWWWWWWWWWWWWW" (by decide +kernel)

end Symconf59
