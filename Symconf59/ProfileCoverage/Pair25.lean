module

public import Symconf59.ProfileMarkedCheck

@[expose] public section

namespace Symconf59

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checkPair_15_15 : pairKeyCoverage 15 15=true :=
  pair_with_marks 15 15 "EEPEPEDEAEEGGGEGGEGGEEGPHHHHHHHHHHHHHHHEHHGHEHIIIPIIIGIIIIIHHHHHHIIPIGHHPEJJJEJEJJJJHHHHHJIJJIJHJEJGHIKKKKEKGGKKKHKKKKIIKKKJKKKEKJLLLLLLLLLLLLLLLLLLLLLLLLLEHEMPEGGPHHHHIMIJMMKKLLMNNNNNNNNNNNNNNNNNLNNOOOOOOOHHOIOOOLOEAEGGHHIIJKLO" (by decide +kernel)
theorem checkPair_16_3 : pairKeyCoverage 16 3=true :=
  pair_with_marks 16 3 "" (by decide +kernel)
theorem checkPair_16_4 : pairKeyCoverage 16 4=true :=
  pair_with_marks 16 4 "QQDD" (by decide +kernel)
theorem checkPair_16_5 : pairKeyCoverage 16 5=true :=
  pair_with_marks 16 5 "FFFQFFQFFQDQDQQQ" (by decide +kernel)
theorem checkPair_16_6 : pairKeyCoverage 16 6=true :=
  pair_with_marks 16 6 "QQDFFFQFFQFQQGQQQDFFQFQGQQQQFFQFQQQQFQQQFQQ" (by decide +kernel)
theorem checkPair_16_7 : pairKeyCoverage 16 7=true :=
  pair_with_marks 16 7 "QHHHHHHHHQHHHHQQHHHHHHQHHQQHHHHHQHQHHHQQHHQQHHQFFQDHQQHHQFQGQHQFQHQQQDFQFDQGFQQQQQDFQQFQQQ" (by decide +kernel)

end Symconf59
