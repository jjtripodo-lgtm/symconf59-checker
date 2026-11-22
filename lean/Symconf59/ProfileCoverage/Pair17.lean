import Symconf59.ProfileMarkedCheck

namespace Symconf59

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checkPair_14_14 : pairKeyCoverage 14 14=true :=
  pair_with_marks 14 14 "EODFFOOEODOEOFFOOEGEOFOEEFOEOOOFFFOEOOFGDOGFOOEFFDDFFEFGDODFFOOIOFFOOFFIOFIIIIIFIODFOOFOOFDOEOFOJEEJFOEJJOJFJOJJJFOFJJFJJOJEFOEOGFEKKEODOKKEGKEKKKEKKKKKOIKKKOKKEKKJKKDOGEILLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLFLJOOFOOOFOOOOFOOMOFFMOOMJMKOKKLLLOMNNNNNNNNNNNNNNNNNNNNNNNNNLLNNFEFFDDFFEFGDIFIJFJKKLLMND" (by decide +kernel)
theorem checkPair_15_3 : pairKeyCoverage 15 3=true :=
  pair_with_marks 15 3 "" (by decide +kernel)
theorem checkPair_15_4 : pairKeyCoverage 15 4=true :=
  pair_with_marks 15 4 "EEPP" (by decide +kernel)
theorem checkPair_15_5 : pairKeyCoverage 15 5=true :=
  pair_with_marks 15 5 "FFFFEFFEFPEPEDEPE" (by decide +kernel)
theorem checkPair_15_6 : pairKeyCoverage 15 6=true :=
  pair_with_marks 15 6 "EEPFFFEFGEGGGEGGEPPFFFEFEGGEEPFFEFEGEPFFEGEFEPF" (by decide +kernel)

end Symconf59
