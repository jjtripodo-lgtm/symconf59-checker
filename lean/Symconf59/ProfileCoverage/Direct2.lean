import Symconf59.ProfileKeyChecker

namespace Symconf59

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem keyCoverage29 : topKeyCoverage 29=true := by decide +kernel

end Symconf59
