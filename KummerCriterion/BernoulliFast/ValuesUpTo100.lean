module

public import Mathlib.NumberTheory.Bernoulli
import KummerCriterion.BernoulliFast.Cbv
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar

/-!
# Concrete Bernoulli values up to `B₁₀₀`

This file caches the even-indexed rational values from `bernoulli 4` through
`bernoulli 94` as `simp` theorems, proved from a certified table.
-/

@[expose] public section

namespace KummerCriterion.BernoulliFast

private def bernoulliTable94 : List Cbv.Frac :=
  [(1, 1),
   (-1, 2),
   (1, 6),
   (0, 1),
   (-1, 30),
   (0, 1),
   (1, 42),
   (0, 1),
   (-1, 30),
   (0, 1),
   (5, 66),
   (0, 1),
   (-691, 2730),
   (0, 1),
   (7, 6),
   (0, 1),
   (-3617, 510),
   (0, 1),
   (43867, 798),
   (0, 1),
   (-174611, 330),
   (0, 1),
   (854513, 138),
   (0, 1),
   (-236364091, 2730),
   (0, 1),
   (8553103, 6),
   (0, 1),
   (-23749461029, 870),
   (0, 1),
   (8615841276005, 14322),
   (0, 1),
   (-7709321041217, 510),
   (0, 1),
   (2577687858367, 6),
   (0, 1),
   (-26315271553053477373, 1919190),
   (0, 1),
   (2929993913841559, 6),
   (0, 1),
   (-261082718496449122051, 13530),
   (0, 1),
   (1520097643918070802691, 1806),
   (0, 1),
   (-27833269579301024235023, 690),
   (0, 1),
   (596451111593912163277961, 282),
   (0, 1),
   (-5609403368997817686249127547, 46410),
   (0, 1),
   (495057205241079648212477525, 66),
   (0, 1),
   (-801165718135489957347924991853, 1590),
   (0, 1),
   (29149963634884862421418123812691, 798),
   (0, 1),
   (-2479392929313226753685415739663229, 870),
   (0, 1),
   (84483613348880041862046775994036021, 354),
   (0, 1),
   (-1215233140483755572040304994079820246041491, 56786730),
   (0, 1),
   (12300585434086858541953039857403386151, 6),
   (0, 1),
   (-106783830147866529886385444979142647942017, 510),
   (0, 1),
   (1472600022126335654051619428551932342241899101, 64722),
   (0, 1),
   (-78773130858718728141909149208474606244347001, 30),
   (0, 1),
   (1505381347333367003803076567377857208511438160235, 4686),
   (0, 1),
   (-5827954961669944110438277244641067365282488301844260429, 140100870),
   (0, 1),
   (34152417289221168014330073731472635186688307783087, 6),
   (0, 1),
   (-24655088825935372707687196040585199904365267828865801, 30),
   (0, 1),
   (414846365575400828295179035549542073492199375372400483487, 3318),
   (0, 1),
   (-4603784299479457646935574969019046849794257872751288919656867, 230010),
   (0, 1),
   (1677014149185145836823154509786269900207736027570253414881613, 498),
   (0, 1),
   (-2024576195935290360231131160111731009989917391198090877281083932477, 3404310),
   (0, 1),
   (660714619417678653573847847426261496277830686653388931761996983, 6),
   (0, 1),
   (-1311426488674017507995511424019311843345750275572028644296919890574047, 61410),
   (0, 1),
   (1179057279021082799884123351249215083775254949669647116231545215727922535, 272118),
   (0, 1),
   (-1295585948207537527989427828538576749659341483719435143023316326829946247, 1410),
   (0, 1),
   (1220813806579744469607301679413201203958508415202696621436215105284649447, 6)]

private theorem bernoulliFracList_94_eq :
    Cbv.bernoulliFracList 94 = bernoulliTable94 := by
  set_option maxRecDepth 100000 in
  decide

private theorem bernoulli_eq_table (k : ℕ) (hk : k ≤ 94) :
    bernoulli k = Cbv.toRat (bernoulliTable94.getD k (0, 1)) := by
  rw [← Cbv.bernoulliFracList_getD_toRat_eq_bernoulli (n := 94) hk]
  rw [bernoulliFracList_94_eq]

@[simp] theorem bernoulli_4 : bernoulli 4 = (-1 / 30 : ℚ) := by
  rw [bernoulli_eq_table _ (by norm_num)]
  norm_num [bernoulliTable94, Cbv.toRat, Rat.mkRat_eq_div]

@[simp] theorem bernoulli_6 : bernoulli 6 = (1 / 42 : ℚ) := by
  rw [bernoulli_eq_table _ (by norm_num)]
  norm_num [bernoulliTable94, Cbv.toRat, Rat.mkRat_eq_div]

@[simp] theorem bernoulli_8 : bernoulli 8 = (-1 / 30 : ℚ) := by
  rw [bernoulli_eq_table _ (by norm_num)]
  norm_num [bernoulliTable94, Cbv.toRat, Rat.mkRat_eq_div]

@[simp] theorem bernoulli_10 : bernoulli 10 = (5 / 66 : ℚ) := by
  rw [bernoulli_eq_table _ (by norm_num)]
  norm_num [bernoulliTable94, Cbv.toRat, Rat.mkRat_eq_div]

@[simp] theorem bernoulli_12 : bernoulli 12 = (-691 / 2730 : ℚ) := by
  rw [bernoulli_eq_table _ (by norm_num)]
  norm_num [bernoulliTable94, Cbv.toRat, Rat.mkRat_eq_div]

@[simp] theorem bernoulli_14 : bernoulli 14 = (7 / 6 : ℚ) := by
  rw [bernoulli_eq_table _ (by norm_num)]
  norm_num [bernoulliTable94, Cbv.toRat, Rat.mkRat_eq_div]

@[simp] theorem bernoulli_16 : bernoulli 16 = (-3617 / 510 : ℚ) := by
  rw [bernoulli_eq_table _ (by norm_num)]
  norm_num [bernoulliTable94, Cbv.toRat, Rat.mkRat_eq_div]

@[simp] theorem bernoulli_18 : bernoulli 18 = (43867 / 798 : ℚ) := by
  rw [bernoulli_eq_table _ (by norm_num)]
  norm_num [bernoulliTable94, Cbv.toRat, Rat.mkRat_eq_div]

@[simp] theorem bernoulli_20 : bernoulli 20 = (-174611 / 330 : ℚ) := by
  rw [bernoulli_eq_table _ (by norm_num)]
  norm_num [bernoulliTable94, Cbv.toRat, Rat.mkRat_eq_div]

@[simp] theorem bernoulli_22 : bernoulli 22 = (854513 / 138 : ℚ) := by
  rw [bernoulli_eq_table _ (by norm_num)]
  norm_num [bernoulliTable94, Cbv.toRat, Rat.mkRat_eq_div]

@[simp] theorem bernoulli_24 : bernoulli 24 = (-236364091 / 2730 : ℚ) := by
  rw [bernoulli_eq_table _ (by norm_num)]
  norm_num [bernoulliTable94, Cbv.toRat, Rat.mkRat_eq_div]

@[simp] theorem bernoulli_26 : bernoulli 26 = (8553103 / 6 : ℚ) := by
  rw [bernoulli_eq_table _ (by norm_num)]
  norm_num [bernoulliTable94, Cbv.toRat, Rat.mkRat_eq_div]

@[simp] theorem bernoulli_28 : bernoulli 28 = (-23749461029 / 870 : ℚ) := by
  rw [bernoulli_eq_table _ (by norm_num)]
  norm_num [bernoulliTable94, Cbv.toRat, Rat.mkRat_eq_div]

@[simp] theorem bernoulli_30 : bernoulli 30 = (8615841276005 / 14322 : ℚ) := by
  rw [bernoulli_eq_table _ (by norm_num)]
  norm_num [bernoulliTable94, Cbv.toRat, Rat.mkRat_eq_div]

@[simp] theorem bernoulli_32 : bernoulli 32 = (-7709321041217 / 510 : ℚ) := by
  rw [bernoulli_eq_table _ (by norm_num)]
  norm_num [bernoulliTable94, Cbv.toRat, Rat.mkRat_eq_div]

@[simp] theorem bernoulli_34 : bernoulli 34 = (2577687858367 / 6 : ℚ) := by
  rw [bernoulli_eq_table _ (by norm_num)]
  norm_num [bernoulliTable94, Cbv.toRat, Rat.mkRat_eq_div]

@[simp] theorem bernoulli_36 : bernoulli 36 =
    (-26315271553053477373 / 1919190 : ℚ) := by
  rw [bernoulli_eq_table _ (by norm_num)]
  norm_num [bernoulliTable94, Cbv.toRat, Rat.mkRat_eq_div]

@[simp] theorem bernoulli_38 : bernoulli 38 = (2929993913841559 / 6 : ℚ) := by
  rw [bernoulli_eq_table _ (by norm_num)]
  norm_num [bernoulliTable94, Cbv.toRat, Rat.mkRat_eq_div]

@[simp] theorem bernoulli_40 : bernoulli 40 =
    (-261082718496449122051 / 13530 : ℚ) := by
  rw [bernoulli_eq_table _ (by norm_num)]
  norm_num [bernoulliTable94, Cbv.toRat, Rat.mkRat_eq_div]

@[simp] theorem bernoulli_42 : bernoulli 42 =
    (1520097643918070802691 / 1806 : ℚ) := by
  rw [bernoulli_eq_table _ (by norm_num)]
  norm_num [bernoulliTable94, Cbv.toRat, Rat.mkRat_eq_div]

@[simp] theorem bernoulli_44 : bernoulli 44 =
    (-27833269579301024235023 / 690 : ℚ) := by
  rw [bernoulli_eq_table _ (by norm_num)]
  norm_num [bernoulliTable94, Cbv.toRat, Rat.mkRat_eq_div]

@[simp] theorem bernoulli_46 : bernoulli 46 =
    (596451111593912163277961 / 282 : ℚ) := by
  rw [bernoulli_eq_table _ (by norm_num)]
  norm_num [bernoulliTable94, Cbv.toRat, Rat.mkRat_eq_div]

@[simp] theorem bernoulli_48 : bernoulli 48 =
    (-5609403368997817686249127547 / 46410 : ℚ) := by
  rw [bernoulli_eq_table _ (by norm_num)]
  norm_num [bernoulliTable94, Cbv.toRat, Rat.mkRat_eq_div]

@[simp] theorem bernoulli_50 : bernoulli 50 =
    (495057205241079648212477525 / 66 : ℚ) := by
  rw [bernoulli_eq_table _ (by norm_num)]
  norm_num [bernoulliTable94, Cbv.toRat, Rat.mkRat_eq_div]

@[simp] theorem bernoulli_52 : bernoulli 52 =
    (-801165718135489957347924991853 / 1590 : ℚ) := by
  rw [bernoulli_eq_table _ (by norm_num)]
  norm_num [bernoulliTable94, Cbv.toRat, Rat.mkRat_eq_div]

@[simp] theorem bernoulli_54 : bernoulli 54 =
    (29149963634884862421418123812691 / 798 : ℚ) := by
  rw [bernoulli_eq_table _ (by norm_num)]
  norm_num [bernoulliTable94, Cbv.toRat, Rat.mkRat_eq_div]

@[simp] theorem bernoulli_56 : bernoulli 56 =
    (-2479392929313226753685415739663229 / 870 : ℚ) := by
  rw [bernoulli_eq_table _ (by norm_num)]
  norm_num [bernoulliTable94, Cbv.toRat, Rat.mkRat_eq_div]

@[simp] theorem bernoulli_58 : bernoulli 58 =
    (84483613348880041862046775994036021 / 354 : ℚ) := by
  rw [bernoulli_eq_table _ (by norm_num)]
  norm_num [bernoulliTable94, Cbv.toRat, Rat.mkRat_eq_div]

@[simp] theorem bernoulli_60 : bernoulli 60 =
    (-1215233140483755572040304994079820246041491 / 56786730 : ℚ) := by
  rw [bernoulli_eq_table _ (by norm_num)]
  norm_num [bernoulliTable94, Cbv.toRat, Rat.mkRat_eq_div]

@[simp] theorem bernoulli_62 : bernoulli 62 =
    (12300585434086858541953039857403386151 / 6 : ℚ) := by
  rw [bernoulli_eq_table _ (by norm_num)]
  norm_num [bernoulliTable94, Cbv.toRat, Rat.mkRat_eq_div]

@[simp] theorem bernoulli_64 : bernoulli 64 =
    (-106783830147866529886385444979142647942017 / 510 : ℚ) := by
  rw [bernoulli_eq_table _ (by norm_num)]
  norm_num [bernoulliTable94, Cbv.toRat, Rat.mkRat_eq_div]

@[simp] theorem bernoulli_66 : bernoulli 66 =
    (1472600022126335654051619428551932342241899101 / 64722 : ℚ) := by
  rw [bernoulli_eq_table _ (by norm_num)]
  norm_num [bernoulliTable94, Cbv.toRat, Rat.mkRat_eq_div]

@[simp] theorem bernoulli_68 : bernoulli 68 =
    (-78773130858718728141909149208474606244347001 / 30 : ℚ) := by
  rw [bernoulli_eq_table _ (by norm_num)]
  norm_num [bernoulliTable94, Cbv.toRat, Rat.mkRat_eq_div]

@[simp] theorem bernoulli_70 : bernoulli 70 =
    (1505381347333367003803076567377857208511438160235 / 4686 : ℚ) := by
  rw [bernoulli_eq_table _ (by norm_num)]
  norm_num [bernoulliTable94, Cbv.toRat, Rat.mkRat_eq_div]

@[simp] theorem bernoulli_72 : bernoulli 72 =
    (-5827954961669944110438277244641067365282488301844260429 / 140100870 : ℚ) := by
  rw [bernoulli_eq_table _ (by norm_num)]
  norm_num [bernoulliTable94, Cbv.toRat, Rat.mkRat_eq_div]

@[simp] theorem bernoulli_74 : bernoulli 74 =
    (34152417289221168014330073731472635186688307783087 / 6 : ℚ) := by
  rw [bernoulli_eq_table _ (by norm_num)]
  norm_num [bernoulliTable94, Cbv.toRat, Rat.mkRat_eq_div]

@[simp] theorem bernoulli_76 : bernoulli 76 =
    (-24655088825935372707687196040585199904365267828865801 / 30 : ℚ) := by
  rw [bernoulli_eq_table _ (by norm_num)]
  norm_num [bernoulliTable94, Cbv.toRat, Rat.mkRat_eq_div]

@[simp] theorem bernoulli_78 : bernoulli 78 =
    (414846365575400828295179035549542073492199375372400483487 / 3318 : ℚ) := by
  rw [bernoulli_eq_table _ (by norm_num)]
  norm_num [bernoulliTable94, Cbv.toRat, Rat.mkRat_eq_div]

@[simp] theorem bernoulli_80 : bernoulli 80 =
    (-4603784299479457646935574969019046849794257872751288919656867 / 230010 : ℚ) := by
  rw [bernoulli_eq_table _ (by norm_num)]
  norm_num [bernoulliTable94, Cbv.toRat, Rat.mkRat_eq_div]

@[simp] theorem bernoulli_82 : bernoulli 82 =
    (1677014149185145836823154509786269900207736027570253414881613 / 498 : ℚ) := by
  rw [bernoulli_eq_table _ (by norm_num)]
  norm_num [bernoulliTable94, Cbv.toRat, Rat.mkRat_eq_div]

@[simp] theorem bernoulli_84 : bernoulli 84 =
    (-2024576195935290360231131160111731009989917391198090877281083932477 /
      3404310 : ℚ) := by
  rw [bernoulli_eq_table _ (by norm_num)]
  norm_num [bernoulliTable94, Cbv.toRat, Rat.mkRat_eq_div]

@[simp] theorem bernoulli_86 : bernoulli 86 =
    (660714619417678653573847847426261496277830686653388931761996983 / 6 : ℚ) := by
  rw [bernoulli_eq_table _ (by norm_num)]
  norm_num [bernoulliTable94, Cbv.toRat, Rat.mkRat_eq_div]

@[simp] theorem bernoulli_88 : bernoulli 88 =
    (-1311426488674017507995511424019311843345750275572028644296919890574047 /
      61410 : ℚ) := by
  rw [bernoulli_eq_table _ (by norm_num)]
  norm_num [bernoulliTable94, Cbv.toRat, Rat.mkRat_eq_div]

@[simp] theorem bernoulli_90 : bernoulli 90 =
    (1179057279021082799884123351249215083775254949669647116231545215727922535 /
      272118 : ℚ) := by
  rw [bernoulli_eq_table _ (by norm_num)]
  norm_num [bernoulliTable94, Cbv.toRat, Rat.mkRat_eq_div]

@[simp] theorem bernoulli_92 : bernoulli 92 =
    (-1295585948207537527989427828538576749659341483719435143023316326829946247 /
      1410 : ℚ) := by
  rw [bernoulli_eq_table _ (by norm_num)]
  norm_num [bernoulliTable94, Cbv.toRat, Rat.mkRat_eq_div]

@[simp] theorem bernoulli_94 : bernoulli 94 =
    (1220813806579744469607301679413201203958508415202696621436215105284649447 /
      6 : ℚ) := by
  rw [bernoulli_eq_table _ (by norm_num)]
  norm_num [bernoulliTable94, Cbv.toRat, Rat.mkRat_eq_div]

end KummerCriterion.BernoulliFast
