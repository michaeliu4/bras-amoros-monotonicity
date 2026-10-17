import Results.Genus.Injection.ExceptionalCounts
import Results.Genus.Injection.Compensation

noncomputable section
namespace SubmittedGenus.OriginalPopulations
open OriginalSources
attribute [local instance] Classical.propDecidable

abbrev FirstTwoAt (g : ℕ) := {d : SourceClass g .E // d.val.val.depth = 4 ∨ uniqueFive d.val.val}
abbrev LastAt (g : ℕ) := {d : SourceClass g .E // ¬ (d.val.val.depth = 4 ∨ uniqueFive d.val.val)}

def firstTwoIntoResidual (g : ℕ) (d : FirstTwoAt g) : FirstResidual ⊕ UniqueFiveResidual :=
  if hd : d.val.val.val.depth = 4 then .inl ⟨d.val.val.val, exceptional_first d.val.property hd⟩
  else .inr ⟨d.val.val.val, exceptional_unique d.val.property hd (d.property.resolve_left hd)⟩

def residualData : FirstResidual ⊕ UniqueFiveResidual → KunzData :=
  Sum.elim (fun d => d.val) (fun d => d.val)

lemma firstTwoIntoResidual_data (g : ℕ) (d : FirstTwoAt g) :
    residualData (firstTwoIntoResidual g d) = d.val.val.val := by
  unfold firstTwoIntoResidual
  split <;> rfl

lemma firstTwoIntoResidual_injective (g : ℕ) : Function.Injective (firstTwoIntoResidual g) := by
  intro d e h
  have he := congrArg residualData h
  rw [firstTwoIntoResidual_data, firstTwoIntoResidual_data] at he
  exact Subtype.ext (Subtype.ext (Subtype.ext he))

lemma firstTwoIntoResidual_weight (g : ℕ) (d : FirstTwoAt g) :
    residualWeight (firstTwoIntoResidual g d) = g := by
  unfold firstTwoIntoResidual
  split <;> exact d.val.val.property

def lastIntoFive (g : ℕ) (d : LastAt g) : CapFiveMass.GenuineFiveAt g :=
  ⟨d.val.val, exceptional_multiple_five d.val.property
    (fun h => d.property (Or.inl h)) (fun h => d.property (Or.inr h))⟩

lemma lastIntoFive_injective (g : ℕ) : Function.Injective (lastIntoFive g) := by
  intro d e he
  exact Subtype.ext (Subtype.ext (congrArg (fun z : CapFiveMass.GenuineFiveAt g => z.val) he))

lemma exceptional_count_split (g : ℕ) :
    Fintype.card (SourceClass g .E) = Fintype.card (FirstTwoAt g) + Fintype.card (LastAt g) := by
  exact (Fintype.card_congr (Equiv.sumCompl
    (fun d : SourceClass g .E => d.val.val.depth = 4 ∨ uniqueFive d.val.val))).symm.trans
    Fintype.card_sum

lemma firstTwo_weighted_count_le {z : ℝ} (hz : 0 < z) (hz1 : z ≤ 1)
    (hs : Summable (fun g => (countFour g : ℝ) * z ^ g)) (g : ℕ) :
    (Fintype.card (FirstTwoAt g) : ℝ) * z ^ g ≤ massFour z := by
  have hd := residualMass_le_massFour hz hz1 hs
  have h := Summable.tsum_le_tsum_of_inj (firstTwoIntoResidual g) (firstTwoIntoResidual_injective g)
    (fun _ _ => pow_nonneg hz.le _) (fun d => le_of_eq (congrArg (fun n => z ^ n)
      (firstTwoIntoResidual_weight g d)).symm)
    (show Summable (fun _ : FirstTwoAt g => z ^ g) from (hasSum_fintype _).summable) hd.1
  have h' : (Fintype.card (FirstTwoAt g) : ℝ) * z ^ g ≤ residualMass z := by
    simpa only [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, residualMass] using h
  exact h'.trans hd.2

/-- The original mass extraction bound, with independently convergent
cap-four and cap-five masses and their separate positive radii. -/
theorem exceptional_mass_extraction (g : ℕ) {z4 z5 : ℝ}
    (hz4 : 0 < z4) (hz41 : z4 ≤ 1) (hz5 : 0 < z5) (_hz51 : z5 ≤ 1)
    (hs4 : Summable (fun n => (countFour n : ℝ) * z4 ^ n))
    (hs5 : Summable (fun n => (CapFiveMass.count n : ℝ) * z5 ^ n)) :
    (Fintype.card (SourceClass g .E) : ℝ) ≤
      massFour z4 / z4 ^ g + CapFiveMass.mass z5 / z5 ^ g := by
  have ha : (Fintype.card (FirstTwoAt g) : ℝ) ≤ massFour z4 / z4 ^ g :=
    (le_div_iff₀ (pow_pos hz4 g)).mpr (firstTwo_weighted_count_le hz4 hz41 hs4 g)
  have hbcard := Fintype.card_le_of_injective (lastIntoFive g) (lastIntoFive_injective g)
  have hbterm : (CapFiveMass.count g : ℝ) * z5 ^ g ≤ CapFiveMass.mass z5 :=
    hs5.le_tsum g (fun n _ => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hz5.le _))
  have hb : (Fintype.card (LastAt g) : ℝ) ≤ CapFiveMass.mass z5 / z5 ^ g := by
    apply (le_div_iff₀ (pow_pos hz5 g)).mpr
    exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hbcard) (pow_nonneg hz5.le g)).trans hbterm
  rw [exceptional_count_split, Nat.cast_add]
  exact add_le_add ha hb

end SubmittedGenus.OriginalPopulations
