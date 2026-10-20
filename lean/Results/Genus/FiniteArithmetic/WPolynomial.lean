import Results.Genus.FiniteArithmetic.CapacityW
import Results.Genus.FiniteArithmetic.SparseArithmetic

set_option maxHeartbeats 3000000
set_option synthInstance.maxSize 1000

namespace SubmittedGenus.FiniteArithmetic
open PowerSeries Reflection

/-- Exact integer terms, checked against the independently proved W source identity below. -/
def wNumeratorTerms : Sparse.Terms := [(4, 1), (5, -3), (6, -1), (7, 7), (9, -3), (10, 2), (11, 2), (12, -31), (13, 15), (14, 59), (15, -42), (16, -98), (17, -53), (18, 54), (19, 39), (20, 374), (21, 582), (22, -236), (23, -1024), (24, 363), (25, 2037), (26, -55), (27, -3111), (28, -6866), (29, -10779), (30, -2072), (31, 20333), (32, 18673), (33, -10243), (34, -10245), (35, 30273), (36, 83321), (37, 125725), (38, 53577), (39, -210720), (40, -393268), (41, -231174), (42, 1099), (43, -33519), (44, -225037), (45, -447707), (46, -459420), (47, 572850), (48, 2655652), (49, 4013737), (50, 3281337), (51, 951505), (52, -2382537), (53, -5872093), (54, -6804739), (55, -4090730), (56, -2172402), (57, -5960078), (58, -13095767), (59, -14964956), (60, -3330473), (61, 23481279), (62, 55005381), (63, 69843625), (64, 50719689), (65, 1274408), (66, -55024417), (67, -92646426), (68, -99082274), (69, -75896294), (70, -31829058), (71, 21673013), (72, 70708625), (73, 100428867), (74, 100727068), (75, 72035916), (76, 25542070), (77, -22603184), (78, -58472034), (79, -74633959), (80, -70718634), (81, -51748047), (82, -25620330), (83, -408322), (84, 17962886), (85, 26974039), (86, 27361778), (87, 21907512), (88, 13942493), (89, 6221098), (90, 395391), (91, -2999028), (92, -4246644), (93, -4043190), (94, -3132298), (95, -2080260), (96, -1203787), (97, -606887), (98, -263473), (99, -96241), (100, -28460), (101, -6388), (102, -965), (103, -73)]
def wDenominatorTail : Sparse.Terms := [(1, -4), (3, 14), (4, -1), (5, -31), (6, 5), (7, 41), (8, -42), (9, 13), (10, 95), (11, -158), (12, -206), (13, 452), (14, 374), (15, -649), (16, -249), (17, 621), (18, -195), (19, -514), (20, 459), (21, -1851), (22, -2887), (23, 3697), (24, 6525), (25, -3074), (26, -5517), (27, 11563), (28, 22397), (29, 12212), (30, -13328), (31, -55900), (32, -77639), (33, -3690), (34, 68920), (35, -61498), (36, -260954), (37, -150434), (38, 311815), (39, 846043), (40, 1115559), (41, 591623), (42, -686301), (43, -1311712), (44, -349413), (45, 636596), (46, -584220), (47, -4336476), (48, -8889804), (49, -10058457), (50, -2382998), (51, 14031918), (52, 28985832), (53, 29816506), (54, 14030590), (55, -6474181), (56, -13529072), (57, -302782), (58, 13355430), (59, -9613431), (60, -84179809), (61, -170294123), (62, -189885236), (63, -88760453), (64, 111236272), (65, 317334473), (66, 423139499), (67, 371359623), (68, 179414355), (69, -79069573), (70, -314029387), (71, -453952107), (72, -464831137), (73, -354396084), (74, -164928851), (75, 43225935), (76, 212749892), (77, 306918772), (78, 317015156), (79, 258731948), (80, 161740908), (81, 57926555), (82, -27709109), (83, -81675373), (84, -102151940), (85, -95888417), (86, -73684346), (87, -46228379), (88, -21417624), (89, -3420313), (90, 6898630), (91, 10835987), (92, 10597216), (93, 8331344), (94, 5608674), (95, 3298418), (96, 1698616), (97, 759725), (98, 290123), (99, 92108), (100, 23358), (101, 4441), (102, 564), (103, 36)]

theorem factorDenominator_5_expanded : factorDenominator 5 = (1 : PowerSeries ℤ) * X^0 + (-4 : PowerSeries ℤ) * X^5 + (-5 : PowerSeries ℤ) * X^6 + (-4 : PowerSeries ℤ) * X^7 + (-3 : PowerSeries ℤ) * X^8 + (-2 : PowerSeries ℤ) * X^9 + (-1 : PowerSeries ℤ) * X^10 := by
  unfold factorDenominator pairPolynomial
  simp only [Fintype.sum_prod_type, Fin.sum_univ_succ]
  norm_num
  ring

theorem factorNumerator_5_expanded : factorNumerator 5 = (1 : PowerSeries ℤ) * X^0 + (1 : PowerSeries ℤ) * X^3 + (1 : PowerSeries ℤ) * X^4 + (1 : PowerSeries ℤ) * X^5 := by
  unfold factorNumerator centerPolynomial
  simp only [Fintype.sum_prod_type, Fin.sum_univ_succ]
  norm_num
  ring

theorem factorDenominator_6_expanded : factorDenominator 6 = (1 : PowerSeries ℤ) * X^0 + (-5 : PowerSeries ℤ) * X^6 + (-6 : PowerSeries ℤ) * X^7 + (-5 : PowerSeries ℤ) * X^8 + (-4 : PowerSeries ℤ) * X^9 + (-3 : PowerSeries ℤ) * X^10 + (-2 : PowerSeries ℤ) * X^11 + (-1 : PowerSeries ℤ) * X^12 := by
  unfold factorDenominator pairPolynomial
  simp only [Fintype.sum_prod_type, Fin.sum_univ_succ]
  norm_num
  ring

theorem factorNumerator_6_expanded : factorNumerator 6 = (1 : PowerSeries ℤ) * X^0 + (1 : PowerSeries ℤ) * X^3 + (1 : PowerSeries ℤ) * X^4 + (1 : PowerSeries ℤ) * X^5 + (1 : PowerSeries ℤ) * X^6 := by
  unfold factorNumerator centerPolynomial
  simp only [Fintype.sum_prod_type, Fin.sum_univ_succ]
  norm_num
  ring

theorem factorDenominator_7_expanded : factorDenominator 7 = (1 : PowerSeries ℤ) * X^0 + (-6 : PowerSeries ℤ) * X^7 + (-7 : PowerSeries ℤ) * X^8 + (-6 : PowerSeries ℤ) * X^9 + (-5 : PowerSeries ℤ) * X^10 + (-4 : PowerSeries ℤ) * X^11 + (-3 : PowerSeries ℤ) * X^12 + (-2 : PowerSeries ℤ) * X^13 + (-1 : PowerSeries ℤ) * X^14 := by
  unfold factorDenominator pairPolynomial
  simp only [Fintype.sum_prod_type, Fin.sum_univ_succ]
  norm_num
  ring

theorem factorNumerator_7_expanded : factorNumerator 7 = (1 : PowerSeries ℤ) * X^0 + (1 : PowerSeries ℤ) * X^4 + (1 : PowerSeries ℤ) * X^5 + (1 : PowerSeries ℤ) * X^6 + (1 : PowerSeries ℤ) * X^7 := by
  unfold factorNumerator centerPolynomial
  simp only [Fintype.sum_prod_type, Fin.sum_univ_succ]
  norm_num
  ring

theorem factorDenominator_8_expanded : factorDenominator 8 = (1 : PowerSeries ℤ) * X^0 + (-7 : PowerSeries ℤ) * X^8 + (-8 : PowerSeries ℤ) * X^9 + (-7 : PowerSeries ℤ) * X^10 + (-6 : PowerSeries ℤ) * X^11 + (-5 : PowerSeries ℤ) * X^12 + (-4 : PowerSeries ℤ) * X^13 + (-3 : PowerSeries ℤ) * X^14 + (-2 : PowerSeries ℤ) * X^15 + (-1 : PowerSeries ℤ) * X^16 := by
  unfold factorDenominator pairPolynomial
  simp only [Fintype.sum_prod_type, Fin.sum_univ_succ]
  norm_num
  ring

theorem factorNumerator_8_expanded : factorNumerator 8 = (1 : PowerSeries ℤ) * X^0 + (1 : PowerSeries ℤ) * X^4 + (1 : PowerSeries ℤ) * X^5 + (1 : PowerSeries ℤ) * X^6 + (1 : PowerSeries ℤ) * X^7 + (1 : PowerSeries ℤ) * X^8 := by
  unfold factorNumerator centerPolynomial
  simp only [Fintype.sum_prod_type, Fin.sum_univ_succ]
  norm_num
  ring

theorem w_denominator_sparse : wPolynomialDenominator = 1 + Sparse.series wDenominatorTail := by
  unfold wPolynomialDenominator mDenominator hPolynomialDenominator jPolynomialDenominator kPolynomialDenominator
  rw [factorDenominator_5_expanded, factorDenominator_6_expanded, factorDenominator_7_expanded, factorDenominator_8_expanded]
  norm_num [Sparse.series, wDenominatorTail, tailDenominator, tailNumerator]
  ring

theorem w_numerator_sparse : wPolynomialNumerator = Sparse.series wNumeratorTerms := by
  unfold wPolynomialNumerator mNumerator mDenominator hPolynomialDenominator jPolynomialDenominator kPolynomialDenominator hPolynomialNumerator jPolynomialNumerator
  rw [factorDenominator_5_expanded, factorDenominator_6_expanded, factorDenominator_7_expanded, factorDenominator_8_expanded, factorNumerator_5_expanded, factorNumerator_6_expanded, factorNumerator_7_expanded, factorNumerator_8_expanded]
  norm_num [Sparse.series, wNumeratorTerms, tailDenominator, tailNumerator]
  ring

theorem wDenominatorTail_positive : ∀ t ∈ wDenominatorTail, 0 < t.1 := by decide

theorem capacityW_sparse_identity :
    (1 + Sparse.series wDenominatorTail) * capacityW = Sparse.series wNumeratorTerms := by
  rw [← w_denominator_sparse, ← w_numerator_sparse]
  exact capacityW_polynomial_identity

#print axioms capacityW_sparse_identity
#print axioms wDenominatorTail_positive

end SubmittedGenus.FiniteArithmetic
