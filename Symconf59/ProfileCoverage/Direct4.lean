module

public import Symconf59.ProfileKeyChecker

@[expose] public section

namespace Symconf59

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem keyCoverage32 : topKeyCoverage 32=true := by decide +kernel
theorem keyCoverage33 : topKeyCoverage 33=true := by decide +kernel
theorem keyCoverage34 : topKeyCoverage 34=true := by decide +kernel

end Symconf59
