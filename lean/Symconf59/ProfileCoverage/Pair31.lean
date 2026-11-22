import Symconf59.ProfileMarkedCheck

namespace Symconf59

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checkPair_16_15 : pairKeyCoverage 16 15=true :=
  pair_with_marks 16 15 "QQPFFQFQQQQPFQGQQPFQQQPQHHHHQQHHQQHQHQQPQQQQPFFFIPFGPFHHHHHPQPFQPHPQPFQJQJQQQPHQQQPFJPPQQPQQKQQQQKQQQKQQKKIKKQJQQPQPLLLLLLLLLLLLLLLLLLLQQQPFQQQPQHQPMPQQQQLPNNNNNNNNNNNNNNLNOOOOOQQOOOOLQQQQQQQIJQN" (by decide +kernel)
theorem checkPair_16_16 : pairKeyCoverage 16 16=true :=
  pair_with_marks 16 16 "QDDFFFQFDQDFFFQQDFQQFQHHHHHHHHHHHHFDHQGEDFFFDFFDHHHHHFDFFHDQJFJQQJFQJHHHJJJJHQFQQKQKDKQQKHKKKKKKQKDHLLLLLLLLLLLLLLLLLFQDFMQFQHHDHQJMLQNNNNNNNNNNNLOOOOQGOOONQPFQPHPQPDFFHDL" (by decide +kernel)
theorem checkPair_17_3 : pairKeyCoverage 17 3=true :=
  pair_with_marks 17 3 "R" (by decide +kernel)
theorem checkPair_17_4 : pairKeyCoverage 17 4=true :=
  pair_with_marks 17 4 "RRR" (by decide +kernel)
theorem checkPair_17_5 : pairKeyCoverage 17 5=true :=
  pair_with_marks 17 5 "RRRRRRRRRRRRRRR" (by decide +kernel)
theorem checkPair_17_6 : pairKeyCoverage 17 6=true :=
  pair_with_marks 17 6 "RRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRR" (by decide +kernel)

end Symconf59
