import Symconf59.ProfileMarkedCheck

namespace Symconf59

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checkPair_24_14 : pairKeyCoverage 24 14=true :=
  pair_with_marks 24 14 "OOOOOOOOOOOOOHFHHFEYOOOOHHOOOOOOYOOOOOKOLYLLYOOOONNNOY" (by decide +kernel)
theorem checkPair_24_15 : pairKeyCoverage 24 15=true :=
  pair_with_marks 24 15 "EPFFEYPFGPFHHHHHPIPFIPHPPFJPPKYKKYLLLYPFPNYOOY" (by decide +kernel)
theorem checkPair_24_16 : pairKeyCoverage 24 16=true :=
  pair_with_marks 24 16 "QQFQQQFQQQHHQQYQFFHQQYJQQQQYLLLQQNNYPQ" (by decide +kernel)
theorem checkPair_24_17 : pairKeyCoverage 24 17=true :=
  pair_with_marks 24 17 "RRRRRRRRRRRRRRRRRRRRRYRRRRYRRYRR" (by decide +kernel)
theorem checkPair_24_18 : pairKeyCoverage 24 18=true :=
  pair_with_marks 24 18 "EFSFSFFHYHHISIJFJKYLLSNOY" (by decide +kernel)
theorem checkPair_24_19 : pairKeyCoverage 24 19=true :=
  pair_with_marks 24 19 "TTTTTTTTTTTTTTYTTYTTY" (by decide +kernel)
theorem checkPair_24_20 : pairKeyCoverage 24 20=true :=
  pair_with_marks 24 20 "UUFYUFUHHUUUUYLUY" (by decide +kernel)
theorem checkPair_24_21 : pairKeyCoverage 24 21=true :=
  pair_with_marks 24 21 "VFVVFHYIVYVLY" (by decide +kernel)
theorem checkPair_24_22 : pairKeyCoverage 24 22=true :=
  pair_with_marks 24 22 "WWWWWWWWWY" (by decide +kernel)
theorem checkPair_24_23 : pairKeyCoverage 24 23=true :=
  pair_with_marks 24 23 "XXXXXXXXX" (by decide +kernel)
theorem checkPair_24_24 : pairKeyCoverage 24 24=true :=
  pair_with_marks 24 24 "EFFHIL" (by decide +kernel)
theorem checkPair_25_3 : pairKeyCoverage 25 3=true :=
  pair_with_marks 25 3 "" (by decide +kernel)
theorem checkPair_25_4 : pairKeyCoverage 25 4=true :=
  pair_with_marks 25 4 "ZZZ" (by decide +kernel)
theorem checkPair_25_5 : pairKeyCoverage 25 5=true :=
  pair_with_marks 25 5 "ZZZZZEDDDE" (by decide +kernel)
theorem checkPair_25_6 : pairKeyCoverage 25 6=true :=
  pair_with_marks 25 6 "ZZZZZZZEGDZZZZGEZZZZZZZ" (by decide +kernel)
theorem checkPair_25_7 : pairKeyCoverage 25 7=true :=
  pair_with_marks 25 7 "ZZZHHHHHHZZHHHHZZHHZHZZZZDEHZZGZZZZDZZZ" (by decide +kernel)
theorem checkPair_25_8 : pairKeyCoverage 25 8=true :=
  pair_with_marks 25 8 "ZZIZIZDIZZIZIIZIIZIZZHHHZHHZZZDZZIZZZZDZZZZZZHHZZZZZ" (by decide +kernel)

end Symconf59
