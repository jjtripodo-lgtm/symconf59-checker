module

public import Symconf59.ProfileKeyChecker

@[expose] public section

namespace Symconf59

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem keyCoverage3 : topKeyCoverage 3=true := by decide +kernel
theorem keyCoverage4 : topKeyCoverage 4=true := by decide +kernel
theorem keyCoverage5 : topKeyCoverage 5=true := by decide +kernel
theorem keyCoverage6 : topKeyCoverage 6=true := by decide +kernel
theorem keyCoverage7 : topKeyCoverage 7=true := by decide +kernel
theorem keyCoverage8 : topKeyCoverage 8=true := by decide +kernel
theorem keyCoverage9 : topKeyCoverage 9=true := by decide +kernel

end Symconf59
