import Symconf59.ProfileMarkedCheck

namespace Symconf59

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checkPair_21_14 : pairKeyCoverage 21 14=true :=
  pair_with_marks 21 14 "OOVOOOOVOOOVOOVOOVEFFEGFFEFGOOVOOOVVIFIVOVOOOVOVOJFOJOVOOVVOKKOVVVLLLLLLLLLOVOOVMVOVNNVNNLEVVOV" (by decide +kernel)
theorem checkPair_21_15 : pairKeyCoverage 21 15=true :=
  pair_with_marks 21 15 "EVFFEVVEFVEVFVEPHHEGPHEPIVFVIVIPIVPEFVVVEPIVVKVVKKKVVVLLLLLLLLVFVPILNVVNVOVOVVVV" (by decide +kernel)
theorem checkPair_21_16 : pairKeyCoverage 21 16=true :=
  pair_with_marks 21 16 "QVFQVVQVFQQVVQHFQQFQQQVFVVFHIVVQVQVQQVVQVVQVQVQLLLLLVQVVQVNVNVVOVVQQV" (by decide +kernel)
theorem checkPair_21_17 : pairKeyCoverage 21 17=true :=
  pair_with_marks 21 17 "RRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRV" (by decide +kernel)
theorem checkPair_21_18 : pairKeyCoverage 21 18=true :=
  pair_with_marks 21 18 "EVFFEVEFVVFESHESSIVFIVSVVFVEIKVVKVLLLLVFVNNOVVVR" (by decide +kernel)
theorem checkPair_21_19 : pairKeyCoverage 21 19=true :=
  pair_with_marks 21 19 "TTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTV" (by decide +kernel)
theorem checkPair_21_20 : pairKeyCoverage 21 20=true :=
  pair_with_marks 21 20 "UVFVVUVVUVHUGUUVVUUVUVVVVLLUVVVUV" (by decide +kernel)
theorem checkPair_21_21 : pairKeyCoverage 21 21=true :=
  pair_with_marks 21 21 "EFFEGFFEFGHIFIJFJKKLLMNOR" (by decide +kernel)
theorem checkPair_22_3 : pairKeyCoverage 22 3=true :=
  pair_with_marks 22 3 "" (by decide +kernel)
theorem checkPair_22_4 : pairKeyCoverage 22 4=true :=
  pair_with_marks 22 4 "WWW" (by decide +kernel)

end Symconf59
