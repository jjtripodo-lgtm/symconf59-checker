module

public import Symconf59.ProfileMarkedCheck

@[expose] public section

namespace Symconf59

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checkPair_20_6 : pairKeyCoverage 20 6=true :=
  pair_with_marks 20 6 "UUDFFGFDUDEGDUUDFFFUGEUUFFFUUUFUUFU" (by decide +kernel)
theorem checkPair_20_7 : pairKeyCoverage 20 7=true :=
  pair_with_marks 20 7 "HHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHUHHHHDHHUHHHGUHHUUDFHDUGFUUDUGU" (by decide +kernel)
theorem checkPair_20_8 : pairKeyCoverage 20 8=true :=
  pair_with_marks 20 8 "UIDFFIFIIDIUDFGIDIIUDFIIUFIUUHHHHHHHUHHHHUHHUUHIHDHIIUIGUUDUFFIDUUGDUUUHHHHHHHUHUUDFIUGUHHDU" (by decide +kernel)
theorem checkPair_20_9 : pairKeyCoverage 20 9=true :=
  pair_with_marks 20 9 "UUJFFFJUJEJUUJFJJUJUJFJJUJJUUHHHHHHHHHHHHHHUJHHUJJUJUUJFIJJUJJIUJJUHHHUHUJIUUJJUHUUUUUFJJUUGFGUJUHHHHHUUUJIUUUUUJFUUHUU" (by decide +kernel)
theorem checkPair_20_10 : pairKeyCoverage 20 10=true :=
  pair_with_marks 20 10 "KKKKKEDDDEKKKKEGDKKGEKKKHHHHHHHHHHHHHKDHHKGKKDIKIKDIIKIIIIIHHHHHDIKKDKHHKKJKJEJKKJJJHHHHKJIJJIJHJKKGHIEDDDEEGDEHHHHHHDIIHDEJJHDEDJ" (by decide +kernel)

end Symconf59
