module

public import Symconf59.ProfileKeyChecker

@[expose] public section

namespace Symconf59

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem keyCoverage30 : topKeyCoverage 30=true := by decide +kernel
theorem keyCoverage31 : topKeyCoverage 31=true := by decide +kernel

end Symconf59
