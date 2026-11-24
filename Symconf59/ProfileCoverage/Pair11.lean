module

public import Symconf59.ProfileMarkedCheck

@[expose] public section

namespace Symconf59

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checkPair_14_7 : pairKeyCoverage 14 7=true :=
  pair_with_marks 14 7 "HHHFFFEHHHDHHEHDHHGFFFEHHHGEHHFFEHHHHHFFEHHFEHFEHDFFFFEHDDEHFFFFEGEHFFEEFFEOEOFFFFEODFGDOGFOOEFFDDFFEFGD" (by decide +kernel)
theorem checkPair_14_8 : pairKeyCoverage 14 8=true :=
  pair_with_marks 14 8 "OOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOIHHFFHHIDHIIHGFFHIGIHFHIIHFIIHDFFFHIHFFFHFFIOFIIIIIFIOOOOOOOOOOOOOOOOOOOOOOOOHHFHHDHGFHHHHIDFIIFIOFOOOOOOOOOOOOOHFHGFDIOOOOHGO" (by decide +kernel)

end Symconf59
