import Symconf59.ProfileMarkedCheck

namespace Symconf59

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checkPair_17_16 : pairKeyCoverage 17 16=true :=
  pair_with_marks 17 16 "RRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRR" (by decide +kernel)
theorem checkPair_17_17 : pairKeyCoverage 17 17=true :=
  pair_with_marks 17 17 "ERFFRDERERFRGEFREHHHHHHHHHHDFFERFFDRFFHHHIRFREJFREJJHHHJFJEHKKERKGKKHKKKKRLLLLLLLLLLLDRFRRHHMJKNNNNNNNNNOOOEOLERPHKQFQQEFI" (by decide +kernel)
theorem checkPair_18_3 : pairKeyCoverage 18 3=true :=
  pair_with_marks 18 3 "" (by decide +kernel)
theorem checkPair_18_4 : pairKeyCoverage 18 4=true :=
  pair_with_marks 18 4 "EES" (by decide +kernel)
theorem checkPair_18_5 : pairKeyCoverage 18 5=true :=
  pair_with_marks 18 5 "FFFSEFFESFEESDS" (by decide +kernel)
theorem checkPair_18_6 : pairKeyCoverage 18 6=true :=
  pair_with_marks 18 6 "EESFFFEFESFSESEEFFFEFEFEEEFFEEFEFFEEFF" (by decide +kernel)
theorem checkPair_18_7 : pairKeyCoverage 18 7=true :=
  pair_with_marks 18 7 "HHHHHHHSHHHHSHHHHHHHHHHHHHHHHHHHHHHHHHHFFHHSEHHFFHHHHFHHFHESFFESEFEEFESFESS" (by decide +kernel)

end Symconf59
