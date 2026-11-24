module

public import Symconf59.ProfileMarkedCheck

@[expose] public section

namespace Symconf59

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checkPair_24_8 : pairKeyCoverage 24 8=true :=
  pair_with_marks 24 8 "IEEFFFIFEIEFFFIIEFIIFIHHHHHHHHHHHHFHHIIEEFFFEFFEHHHHHFEFFHI" (by decide +kernel)
theorem checkPair_24_9 : pairKeyCoverage 24 9=true :=
  pair_with_marks 24 9 "EJFFFJJJEJFFFJJFJJFHHHHHHHHHHJFHJYIJFJJIJFIJHHHJJJJHEFFFJFFHYHHIFIJFI" (by decide +kernel)
theorem checkPair_24_10 : pairKeyCoverage 24 10=true :=
  pair_with_marks 24 10 "KKKKKKEYKKKKGKKKKKKHHHKKHKKKKKKKKKKKKKKHKKKKKKKKKKJKKHKKKKKYKKEYKGKHHKHKJY" (by decide +kernel)
theorem checkPair_24_11 : pairKeyCoverage 24 11=true :=
  pair_with_marks 24 11 "LLLLLLLLLLLLLLLLLLLLLLLLLLYLLLLLLLLLLLLLLLLLLYLLLLLLLLLLLLLLLYLLYLLFLLHHFJK" (by decide +kernel)
theorem checkPair_24_12 : pairKeyCoverage 24 12=true :=
  pair_with_marks 24 12 "EEFFFFMEFFFEFFHHHHHHHHFHIEFIIFIHHMHJFJJFHJIJFKKKKKKKKKLLLLLLLLEFFHIL" (by decide +kernel)
theorem checkPair_24_13 : pairKeyCoverage 24 13=true :=
  pair_with_marks 24 13 "NNNNNNNNNNNNNNNNYNNNNNNNNNNNNNNNNNNNNNNNNNNNYNNLLLLLYNNNNNNFNY" (by decide +kernel)

end Symconf59
