import Symconf59.ProfileMarkedCheck

namespace Symconf59

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checkPair_18_15 : pairKeyCoverage 18 15=true :=
  pair_with_marks 18 15 "ESFFESESEPFFESEFEPFHHHHSHHHHHSEHPSISFSIIPFIPHHHSSSPHEFJEPFJHHPPIJIPFPKSKSKSKKSKSISKKKPLLLLLLLLLLLLLLSSFSPFHSIPMSLNNNNNNNNNSOOOOOSOOOESSSIL" (by decide +kernel)
theorem checkPair_18_16 : pairKeyCoverage 18 16=true :=
  pair_with_marks 18 16 "QSFSQFQSQSFQSQFQQQHHSQQHHQQHQQSSFSFSFFHSHHQSSQJFQQQQQHQJFJQQQKQSQSQSQKSQQSLLLLLLLLLLLQQSQQQQSQQNNNNNNNNNOOOSOLQSPQSQSQQ" (by decide +kernel)
theorem checkPair_18_17 : pairKeyCoverage 18 17=true :=
  pair_with_marks 18 17 "RRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRES" (by decide +kernel)
theorem checkPair_18_18 : pairKeyCoverage 18 18=true :=
  pair_with_marks 18 18 "EDFFEEDEFFEEFFHHHHHHHHFHIDFIIFIHHIHEFEEFHHIIFKKKKKKIKKLLLLLLLLEFFHILNNNNNOOOOPFPQQRRF" (by decide +kernel)
theorem checkPair_19_3 : pairKeyCoverage 19 3=true :=
  pair_with_marks 19 3 "" (by decide +kernel)
theorem checkPair_19_4 : pairKeyCoverage 19 4=true :=
  pair_with_marks 19 4 "TTTT" (by decide +kernel)

end Symconf59
