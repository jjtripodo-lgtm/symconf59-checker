module

public import Symconf59.ProfileKeyChecker

@[expose] public section

namespace Symconf59

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem keyCoverage11 : topKeyCoverage 11=true := by decide +kernel

end Symconf59
