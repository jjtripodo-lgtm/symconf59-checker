import Symconf59.ProfileMarkedCheck

namespace Symconf59

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checkPair_20_14 : pairKeyCoverage 20 14=true :=
  pair_with_marks 20 14 "OOOOOOOOOOOOOOOOOUHHHDUGHUUDUGUOOOOOOOUIGUOOOOOOOOOOUJUOOOOUOOOOOOOKDOIOOOLLLLLLLLLLLOOOOOUUOOONNNNNNNNNDOGUUL" (by decide +kernel)
theorem checkPair_20_15 : pairKeyCoverage 20 15=true :=
  pair_with_marks 20 15 "UUPEDDUEUPEGGUPEUUHHHHHHHUHPUUPDIUIPUHUPUUUPEJUJUPHUUUUKKEPGHPIPJPLLLLLLLLLUPDUUHPUUNNNNNLOOOUOUEUU" (by decide +kernel)
theorem checkPair_20_16 : pairKeyCoverage 20 16=true :=
  pair_with_marks 20 16 "UDQFQQQUQGQUQQHHHQHQHUQUUDFIUGUHHDUUQJJQHUUUQQQQQQQIJQLLLLLLLLDQQHULNNNNNOOOOPQUDU" (by decide +kernel)
theorem checkPair_20_17 : pairKeyCoverage 20 17=true :=
  pair_with_marks 20 17 "RRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRR" (by decide +kernel)
theorem checkPair_20_18 : pairKeyCoverage 20 18=true :=
  pair_with_marks 20 18 "USFSDSUSFSUFUHHSHHUSUSIUUUSUJFUUHUUKSSSILLLLLUSUUNNNOSUUSRU" (by decide +kernel)

end Symconf59
