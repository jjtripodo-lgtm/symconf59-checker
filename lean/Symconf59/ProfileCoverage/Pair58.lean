import Symconf59.ProfileMarkedCheck

namespace Symconf59

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checkPair_25_9 : pairKeyCoverage 25 9=true :=
  pair_with_marks 25 9 "ZZZJZJEJZZZZJZJJZZZHHHZZHZZZZJZZIJJZIJZHZZZJZZZZZZGZZHZZIZZZ" (by decide +kernel)
theorem checkPair_25_10 : pairKeyCoverage 25 10=true :=
  pair_with_marks 25 10 "ZZZEDDDEZZEGDZZEZZZHHHZHHZHZZZZDIZIZZHZZDZZZEJZJZZHZZZZZZEZZZZZZJZ" (by decide +kernel)
theorem checkPair_25_11 : pairKeyCoverage 25 11=true :=
  pair_with_marks 25 11 "LLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLZZDZZHZZ" (by decide +kernel)
theorem checkPair_25_12 : pairKeyCoverage 25 12=true :=
  pair_with_marks 25 12 "ZZZZZDZZZZZZZZZHHZHZZZZIMZIZZZZZJMZZZMZZZZZZHZZLLLLLZZMZZZ" (by decide +kernel)
theorem checkPair_25_13 : pairKeyCoverage 25 13=true :=
  pair_with_marks 25 13 "NNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNLLLLLNNNNZDZ" (by decide +kernel)
theorem checkPair_25_14 : pairKeyCoverage 25 14=true :=
  pair_with_marks 25 14 "ZZOOOOZOOZOZZDZZZZZOZZIZZOOZZZOZZZLLLLZOZNNZZ" (by decide +kernel)
theorem checkPair_25_15 : pairKeyCoverage 25 15=true :=
  pair_with_marks 25 15 "ZZZZEZGGZZZHZZZZIIZZZJZZZEZZLLLZZNNOZ" (by decide +kernel)
theorem checkPair_25_16 : pairKeyCoverage 25 16=true :=
  pair_with_marks 25 16 "ZZZZQZZZZZZQQZZIZZZJZZZQZLLZZNZZ" (by decide +kernel)
theorem checkPair_25_17 : pairKeyCoverage 25 17=true :=
  pair_with_marks 25 17 "RRRRRRRRRRRRRRRRRRRRRRRRZ" (by decide +kernel)

end Symconf59
