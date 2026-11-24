module

public import Symconf59.ProfileMarkedCheck

@[expose] public section

namespace Symconf59

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checkPair_12_3 : pairKeyCoverage 12 3=true :=
  pair_with_marks 12 3 "" (by decide +kernel)
theorem checkPair_12_4 : pairKeyCoverage 12 4=true :=
  pair_with_marks 12 4 "EEED" (by decide +kernel)
theorem checkPair_12_5 : pairKeyCoverage 12 5=true :=
  pair_with_marks 12 5 "FFFFFFFFFFFFDEDEMMD" (by decide +kernel)
theorem checkPair_12_6 : pairKeyCoverage 12 6=true :=
  pair_with_marks 12 6 "EEGFFFFFFFFFFFEGDGEEGFFFFFFFFFEMEEFFFFFFFEEEFFFFFEFFFEFF" (by decide +kernel)
theorem checkPair_12_7 : pairKeyCoverage 12 7=true :=
  pair_with_marks 12 7 "HHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHFFFHHHHHHHHHHFFHHHHHHFFHHHHFHHFHHHFFFFDHHGFFFGHFFHFEDFFMEFFEHMFGMM" (by decide +kernel)
theorem checkPair_12_8 : pairKeyCoverage 12 8=true :=
  pair_with_marks 12 8 "IIIDFFFFFIFFIDIIMIIGFFFFFIFIGIIIGFFFIFIIIFFFIIIFIIFIHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHFFIHHMHHFIHHFIHIHFFIIGFIIDFFMIIDFFFFFFDIIGFFFFFIIGFFFIFFIHHHHHHHHHHHHHHHHHHHFFHHFFHMGMIDFFFFMIFFFGFFHHHHHHHHFHIDFMIFIHHDH" (by decide +kernel)

end Symconf59
