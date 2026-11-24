module

public import Symconf59.ProfileMarkedCheck

@[expose] public section

namespace Symconf59

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checkPair_13_13 : pairKeyCoverage 13 13=true :=
  pair_with_marks 13 13 "NNNFFFNDNNENDNNNFFNNGENNFFNNNNFNNFNHHHHHHHHHHHHHHHHHHHEDFNEEFNENNFNNFNNFFIDNINNFIGNFINHHHHHHHHHHDFFNNFFDNFFHHHDNFNNNJFFNNJNNFJNNJFNJHHHHHHHEJJNNJFINJJHHHJFJNNFNNFNHHNHNGKKNNENDKNGEKNNKKHHKHKKEKKKNIKGKKHKKKNJKNKKKKNENDEHHIJDLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLDFFHINNNFFNNNNFNNFNHHHHHNMNFINHHMNJFNJHJNKNNKKLLLLLNFNJENFFENEFGGFHHHHHGINFIIHNJFJHIKNKKKLLLLNFMDH" (by decide +kernel)
theorem checkPair_14_3 : pairKeyCoverage 14 3=true :=
  pair_with_marks 14 3 "O" (by decide +kernel)
theorem checkPair_14_4 : pairKeyCoverage 14 4=true :=
  pair_with_marks 14 4 "OOO" (by decide +kernel)
theorem checkPair_14_5 : pairKeyCoverage 14 5=true :=
  pair_with_marks 14 5 "OOOOOOOOOOOOOOOOOO" (by decide +kernel)
theorem checkPair_14_6 : pairKeyCoverage 14 6=true :=
  pair_with_marks 14 6 "OOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOO" (by decide +kernel)

end Symconf59
