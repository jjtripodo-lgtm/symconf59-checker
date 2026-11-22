import Symconf59.ProfileKeyChecker

namespace Symconf59

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem all_key_valid : ∀ a : Fin 60, keyValid a.val=true := by decide +kernel

end Symconf59
