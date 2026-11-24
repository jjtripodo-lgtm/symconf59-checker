module

public import Symconf59.ProfileCoverage.Pair00
public import Symconf59.ProfileCoverage.Pair01
public import Symconf59.ProfileCoverage.Pair02
public import Symconf59.ProfileCoverage.Pair03
public import Symconf59.ProfileCoverage.Pair04
public import Symconf59.ProfileCoverage.Pair05
public import Symconf59.ProfileCoverage.Pair06
public import Symconf59.ProfileCoverage.Pair07
public import Symconf59.ProfileCoverage.Pair08
public import Symconf59.ProfileCoverage.Pair09
public import Symconf59.ProfileCoverage.Pair10
public import Symconf59.ProfileCoverage.Pair11
public import Symconf59.ProfileCoverage.Pair12
public import Symconf59.ProfileCoverage.Pair13
public import Symconf59.ProfileCoverage.Pair14
public import Symconf59.ProfileCoverage.Pair15
public import Symconf59.ProfileCoverage.Pair16
public import Symconf59.ProfileCoverage.Pair17
public import Symconf59.ProfileCoverage.Pair18
public import Symconf59.ProfileCoverage.Pair19
public import Symconf59.ProfileCoverage.Pair20
public import Symconf59.ProfileCoverage.Pair21
public import Symconf59.ProfileCoverage.Pair22
public import Symconf59.ProfileCoverage.Pair23
public import Symconf59.ProfileCoverage.Pair24
public import Symconf59.ProfileCoverage.Pair25
public import Symconf59.ProfileCoverage.Pair26
public import Symconf59.ProfileCoverage.Pair27
public import Symconf59.ProfileCoverage.Pair28
public import Symconf59.ProfileCoverage.Pair29
public import Symconf59.ProfileCoverage.Pair30
public import Symconf59.ProfileCoverage.Pair31
public import Symconf59.ProfileCoverage.Pair32
public import Symconf59.ProfileCoverage.Pair33
public import Symconf59.ProfileCoverage.Pair34
public import Symconf59.ProfileCoverage.Pair35
public import Symconf59.ProfileCoverage.Pair36
public import Symconf59.ProfileCoverage.Pair37
public import Symconf59.ProfileCoverage.Pair38
public import Symconf59.ProfileCoverage.Pair39
public import Symconf59.ProfileCoverage.Pair40
public import Symconf59.ProfileCoverage.Pair41
public import Symconf59.ProfileCoverage.Pair42
public import Symconf59.ProfileCoverage.Pair43
public import Symconf59.ProfileCoverage.Pair44
public import Symconf59.ProfileCoverage.Pair45
public import Symconf59.ProfileCoverage.Pair46
public import Symconf59.ProfileCoverage.Pair47
public import Symconf59.ProfileCoverage.Pair48
public import Symconf59.ProfileCoverage.Pair49
public import Symconf59.ProfileCoverage.Pair50
public import Symconf59.ProfileCoverage.Pair51
public import Symconf59.ProfileCoverage.Pair52
public import Symconf59.ProfileCoverage.Pair53
public import Symconf59.ProfileCoverage.Pair54
public import Symconf59.ProfileCoverage.Pair55
public import Symconf59.ProfileCoverage.Pair56
public import Symconf59.ProfileCoverage.Pair57
public import Symconf59.ProfileCoverage.Pair58
public import Symconf59.ProfileCoverage.Pair59
public import Symconf59.ProfileCoverage.Pair60
public import Mathlib.Tactic.IntervalCases

@[expose] public section

namespace Symconf59

theorem keyCoverage12 : topKeyCoverage 12=true := by
  suffices h : ∀ b : ℕ, 3≤b → b≤12 → pairKeyCoverage 12 b=true by
    exact top_from_pair (a:=12) (by decide) (fun b hb1 hb2 _ => h b.val hb1 hb2)
  intro b hb1 hb2
  interval_cases b
  · exact checkPair_12_3
  · exact checkPair_12_4
  · exact checkPair_12_5
  · exact checkPair_12_6
  · exact checkPair_12_7
  · exact checkPair_12_8
  · exact checkPair_12_9
  · exact checkPair_12_10
  · exact checkPair_12_11
  · exact checkPair_12_12

theorem keyCoverage13 : topKeyCoverage 13=true := by
  suffices h : ∀ b : ℕ, 3≤b → b≤13 → pairKeyCoverage 13 b=true by
    exact top_from_pair (a:=13) (by decide) (fun b hb1 hb2 _ => h b.val hb1 hb2)
  intro b hb1 hb2
  interval_cases b
  · exact checkPair_13_3
  · exact checkPair_13_4
  · exact checkPair_13_5
  · exact checkPair_13_6
  · exact checkPair_13_7
  · exact checkPair_13_8
  · exact checkPair_13_9
  · exact checkPair_13_10
  · exact checkPair_13_11
  · exact checkPair_13_12
  · exact checkPair_13_13

theorem keyCoverage14 : topKeyCoverage 14=true := by
  suffices h : ∀ b : ℕ, 3≤b → b≤14 → pairKeyCoverage 14 b=true by
    exact top_from_pair (a:=14) (by decide) (fun b hb1 hb2 _ => h b.val hb1 hb2)
  intro b hb1 hb2
  interval_cases b
  · exact checkPair_14_3
  · exact checkPair_14_4
  · exact checkPair_14_5
  · exact checkPair_14_6
  · exact checkPair_14_7
  · exact checkPair_14_8
  · exact checkPair_14_9
  · exact checkPair_14_10
  · exact checkPair_14_11
  · exact checkPair_14_12
  · exact checkPair_14_13
  · exact checkPair_14_14

theorem keyCoverage15 : topKeyCoverage 15=true := by
  suffices h : ∀ b : ℕ, 3≤b → b≤15 → pairKeyCoverage 15 b=true by
    exact top_from_pair (a:=15) (by decide) (fun b hb1 hb2 _ => h b.val hb1 hb2)
  intro b hb1 hb2
  interval_cases b
  · exact checkPair_15_3
  · exact checkPair_15_4
  · exact checkPair_15_5
  · exact checkPair_15_6
  · exact checkPair_15_7
  · exact checkPair_15_8
  · exact checkPair_15_9
  · exact checkPair_15_10
  · exact checkPair_15_11
  · exact checkPair_15_12
  · exact checkPair_15_13
  · exact checkPair_15_14
  · exact checkPair_15_15

theorem keyCoverage16 : topKeyCoverage 16=true := by
  suffices h : ∀ b : ℕ, 3≤b → b≤16 → pairKeyCoverage 16 b=true by
    exact top_from_pair (a:=16) (by decide) (fun b hb1 hb2 _ => h b.val hb1 hb2)
  intro b hb1 hb2
  interval_cases b
  · exact checkPair_16_3
  · exact checkPair_16_4
  · exact checkPair_16_5
  · exact checkPair_16_6
  · exact checkPair_16_7
  · exact checkPair_16_8
  · exact checkPair_16_9
  · exact checkPair_16_10
  · exact checkPair_16_11
  · exact checkPair_16_12
  · exact checkPair_16_13
  · exact checkPair_16_14
  · exact checkPair_16_15
  · exact checkPair_16_16

theorem keyCoverage17 : topKeyCoverage 17=true := by
  suffices h : ∀ b : ℕ, 3≤b → b≤17 → pairKeyCoverage 17 b=true by
    exact top_from_pair (a:=17) (by decide) (fun b hb1 hb2 _ => h b.val hb1 hb2)
  intro b hb1 hb2
  interval_cases b
  · exact checkPair_17_3
  · exact checkPair_17_4
  · exact checkPair_17_5
  · exact checkPair_17_6
  · exact checkPair_17_7
  · exact checkPair_17_8
  · exact checkPair_17_9
  · exact checkPair_17_10
  · exact checkPair_17_11
  · exact checkPair_17_12
  · exact checkPair_17_13
  · exact checkPair_17_14
  · exact checkPair_17_15
  · exact checkPair_17_16
  · exact checkPair_17_17

theorem keyCoverage18 : topKeyCoverage 18=true := by
  suffices h : ∀ b : ℕ, 3≤b → b≤18 → pairKeyCoverage 18 b=true by
    exact top_from_pair (a:=18) (by decide) (fun b hb1 hb2 _ => h b.val hb1 hb2)
  intro b hb1 hb2
  interval_cases b
  · exact checkPair_18_3
  · exact checkPair_18_4
  · exact checkPair_18_5
  · exact checkPair_18_6
  · exact checkPair_18_7
  · exact checkPair_18_8
  · exact checkPair_18_9
  · exact checkPair_18_10
  · exact checkPair_18_11
  · exact checkPair_18_12
  · exact checkPair_18_13
  · exact checkPair_18_14
  · exact checkPair_18_15
  · exact checkPair_18_16
  · exact checkPair_18_17
  · exact checkPair_18_18

theorem keyCoverage19 : topKeyCoverage 19=true := by
  suffices h : ∀ b : ℕ, 3≤b → b≤19 → pairKeyCoverage 19 b=true by
    exact top_from_pair (a:=19) (by decide) (fun b hb1 hb2 _ => h b.val hb1 hb2)
  intro b hb1 hb2
  interval_cases b
  · exact checkPair_19_3
  · exact checkPair_19_4
  · exact checkPair_19_5
  · exact checkPair_19_6
  · exact checkPair_19_7
  · exact checkPair_19_8
  · exact checkPair_19_9
  · exact checkPair_19_10
  · exact checkPair_19_11
  · exact checkPair_19_12
  · exact checkPair_19_13
  · exact checkPair_19_14
  · exact checkPair_19_15
  · exact checkPair_19_16
  · exact checkPair_19_17
  · exact checkPair_19_18
  · exact checkPair_19_19

theorem keyCoverage20 : topKeyCoverage 20=true := by
  suffices h : ∀ b : ℕ, 3≤b → b≤20 → pairKeyCoverage 20 b=true by
    exact top_from_pair (a:=20) (by decide) (fun b hb1 hb2 _ => h b.val hb1 hb2)
  intro b hb1 hb2
  interval_cases b
  · exact checkPair_20_3
  · exact checkPair_20_4
  · exact checkPair_20_5
  · exact checkPair_20_6
  · exact checkPair_20_7
  · exact checkPair_20_8
  · exact checkPair_20_9
  · exact checkPair_20_10
  · exact checkPair_20_11
  · exact checkPair_20_12
  · exact checkPair_20_13
  · exact checkPair_20_14
  · exact checkPair_20_15
  · exact checkPair_20_16
  · exact checkPair_20_17
  · exact checkPair_20_18
  · exact checkPair_20_19
  · exact checkPair_20_20

theorem keyCoverage21 : topKeyCoverage 21=true := by
  suffices h : ∀ b : ℕ, 3≤b → b≤21 → pairKeyCoverage 21 b=true by
    exact top_from_pair (a:=21) (by decide) (fun b hb1 hb2 _ => h b.val hb1 hb2)
  intro b hb1 hb2
  interval_cases b
  · exact checkPair_21_3
  · exact checkPair_21_4
  · exact checkPair_21_5
  · exact checkPair_21_6
  · exact checkPair_21_7
  · exact checkPair_21_8
  · exact checkPair_21_9
  · exact checkPair_21_10
  · exact checkPair_21_11
  · exact checkPair_21_12
  · exact checkPair_21_13
  · exact checkPair_21_14
  · exact checkPair_21_15
  · exact checkPair_21_16
  · exact checkPair_21_17
  · exact checkPair_21_18
  · exact checkPair_21_19
  · exact checkPair_21_20
  · exact checkPair_21_21

theorem keyCoverage22 : topKeyCoverage 22=true := by
  suffices h : ∀ b : ℕ, 3≤b → b≤22 → pairKeyCoverage 22 b=true by
    exact top_from_pair (a:=22) (by decide) (fun b hb1 hb2 _ => h b.val hb1 hb2)
  intro b hb1 hb2
  interval_cases b
  · exact checkPair_22_3
  · exact checkPair_22_4
  · exact checkPair_22_5
  · exact checkPair_22_6
  · exact checkPair_22_7
  · exact checkPair_22_8
  · exact checkPair_22_9
  · exact checkPair_22_10
  · exact checkPair_22_11
  · exact checkPair_22_12
  · exact checkPair_22_13
  · exact checkPair_22_14
  · exact checkPair_22_15
  · exact checkPair_22_16
  · exact checkPair_22_17
  · exact checkPair_22_18
  · exact checkPair_22_19
  · exact checkPair_22_20
  · exact checkPair_22_21
  · exact checkPair_22_22

theorem keyCoverage23 : topKeyCoverage 23=true := by
  suffices h : ∀ b : ℕ, 3≤b → b≤23 → pairKeyCoverage 23 b=true by
    exact top_from_pair (a:=23) (by decide) (fun b hb1 hb2 _ => h b.val hb1 hb2)
  intro b hb1 hb2
  interval_cases b
  · exact checkPair_23_3
  · exact checkPair_23_4
  · exact checkPair_23_5
  · exact checkPair_23_6
  · exact checkPair_23_7
  · exact checkPair_23_8
  · exact checkPair_23_9
  · exact checkPair_23_10
  · exact checkPair_23_11
  · exact checkPair_23_12
  · exact checkPair_23_13
  · exact checkPair_23_14
  · exact checkPair_23_15
  · exact checkPair_23_16
  · exact checkPair_23_17
  · exact checkPair_23_18
  · exact checkPair_23_19
  · exact checkPair_23_20
  · exact checkPair_23_21
  · exact checkPair_23_22
  · exact checkPair_23_23

theorem keyCoverage24 : topKeyCoverage 24=true := by
  suffices h : ∀ b : ℕ, 3≤b → b≤24 → pairKeyCoverage 24 b=true by
    exact top_from_pair (a:=24) (by decide) (fun b hb1 hb2 _ => h b.val hb1 hb2)
  intro b hb1 hb2
  interval_cases b
  · exact checkPair_24_3
  · exact checkPair_24_4
  · exact checkPair_24_5
  · exact checkPair_24_6
  · exact checkPair_24_7
  · exact checkPair_24_8
  · exact checkPair_24_9
  · exact checkPair_24_10
  · exact checkPair_24_11
  · exact checkPair_24_12
  · exact checkPair_24_13
  · exact checkPair_24_14
  · exact checkPair_24_15
  · exact checkPair_24_16
  · exact checkPair_24_17
  · exact checkPair_24_18
  · exact checkPair_24_19
  · exact checkPair_24_20
  · exact checkPair_24_21
  · exact checkPair_24_22
  · exact checkPair_24_23
  · exact checkPair_24_24

theorem keyCoverage25 : topKeyCoverage 25=true := by
  suffices h : ∀ b : ℕ, 3≤b → b≤25 → pairKeyCoverage 25 b=true by
    exact top_from_pair (a:=25) (by decide) (fun b hb1 hb2 _ => h b.val hb1 hb2)
  intro b hb1 hb2
  interval_cases b
  · exact checkPair_25_3
  · exact checkPair_25_4
  · exact checkPair_25_5
  · exact checkPair_25_6
  · exact checkPair_25_7
  · exact checkPair_25_8
  · exact checkPair_25_9
  · exact checkPair_25_10
  · exact checkPair_25_11
  · exact checkPair_25_12
  · exact checkPair_25_13
  · exact checkPair_25_14
  · exact checkPair_25_15
  · exact checkPair_25_16
  · exact checkPair_25_17
  · exact checkPair_25_18
  · exact checkPair_25_19
  · exact checkPair_25_20
  · exact checkPair_25_21
  · exact checkPair_25_22
  · exact checkPair_25_23
  · exact checkPair_25_24
  · exact checkPair_25_25

theorem keyCoverage26 : topKeyCoverage 26=true := by
  suffices h : ∀ b : ℕ, 3≤b → b≤26 → pairKeyCoverage 26 b=true by
    exact top_from_pair (a:=26) (by decide) (fun b hb1 hb2 _ => h b.val hb1 hb2)
  intro b hb1 hb2
  interval_cases b
  · exact checkPair_26_3
  · exact checkPair_26_4
  · exact checkPair_26_5
  · exact checkPair_26_6
  · exact checkPair_26_7
  · exact checkPair_26_8
  · exact checkPair_26_9
  · exact checkPair_26_10
  · exact checkPair_26_11
  · exact checkPair_26_12
  · exact checkPair_26_13
  · exact checkPair_26_14
  · exact checkPair_26_15
  · exact checkPair_26_16
  · exact checkPair_26_17
  · exact checkPair_26_18
  · exact checkPair_26_19
  · exact checkPair_26_20
  · exact checkPair_26_21
  · exact checkPair_26_22
  · exact checkPair_26_23
  · exact checkPair_26_24
  · exact checkPair_26_25
  · exact checkPair_26_26

end Symconf59
