import Results.Genus.CapFourMass.ConditionalDensity

namespace SubmittedGenus.CapFourMass.ActualConditionalDensity
open scoped BigOperators
open RawGraph ContractionGeometry GadgetCoordinates GadgetFibers GadgetLocalSums ConditionalDensity
noncomputable section
attribute [local instance] Classical.propDecidable

theorem nonpostponed_four {m r p i : ℕ} (hr : 1 ≤ r) (hrp : r < p)
    (hi : Eligible m p i) (hnr : 2*i ≠ m+r-i) (hnp : 2*i ≠ m+p-i)
    {z : ℝ} (hz : 0 < z) (J : Finset ℕ)
    (hJ : ∀j∈J,Eligible m p j) (hne : ∀j∈J,i≠j)
    (horder : ∀j∈J,¬Arrow m r p i j)
    : LocalWeights.epsilon z*(∑ x, if Good m r p J x then ∏ v, z^(x v).val else 0) ≤
      ∑ x, if Good m r p J x ∧ Failure (KunzWord.coord (boundedWord x)) i
        then ∏ v, z^(x v).val else 0 := by
  let e := equiv4 hr hrp hi hnr hnp
  have hc : physical (e 0).val=i := by norm_num [e,equiv4_physical,label4]
  have ht : physical (e 1).val=2*i := by
    norm_num [e,equiv4_physical,label4,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail]
  apply nonpostponed_model hr hrp hi e 0 1 hc ht z (LocalWeights.epsilon z) (le_of_lt hz) (le_of_lt (LocalWeights.epsilon_pos hz)) J hJ hne horder allowedFour failureFour
  · intro b a ha
    exact GadgetSourceBounds.allowed_four hr hrp hi hnr hnp a b ha
  · intro a ha
    rcases ha with ⟨h0,h1,h2,h3⟩
    refine ⟨h0,h1,?_⟩
    intro k hk
    fin_cases k <;> simp_all [letter]
  · exact four_density hz

theorem nonpostponed_left {m r p i : ℕ} (hr : 1 ≤ r) (hrp : r < p)
    (hi : Eligible m p i) (hs : 2*i=m+r-i)
    {z : ℝ} (hz : 0 < z) (J : Finset ℕ)
    (hJ : ∀j∈J,Eligible m p j) (hne : ∀j∈J,i≠j)
    (horder : ∀j∈J,¬Arrow m r p i j)
    : LocalWeights.epsilon z*(∑ x, if Good m r p J x then ∏ v, z^(x v).val else 0) ≤
      ∑ x, if Good m r p J x ∧ Failure (KunzWord.coord (boundedWord x)) i
        then ∏ v, z^(x v).val else 0 := by
  let e := equiv3 hr hrp hi (Or.inl hs)
  have hc : physical (e 0).val=i := by norm_num [e,equiv3_physical,label3]
  have ht : physical (e 1).val=2*i := by
    norm_num [e,equiv3_physical,label3,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail]
    omega
  apply nonpostponed_model hr hrp hi e 0 1 hc ht z (LocalWeights.epsilon z) (le_of_lt hz) (le_of_lt (LocalWeights.epsilon_pos hz)) J hJ hne horder allowedThree failureThreeLeft
  · intro b a ha
    exact GadgetSourceBounds.allowed_three hr hrp hi (Or.inl hs) a b ha
  · intro a ha
    rcases ha with ⟨h0,ht,hl⟩
    refine ⟨h0,ht,?_⟩
    intro k hk
    fin_cases k <;> simp_all [letter]
  · exact three_left_density hz

theorem nonpostponed_right {m r p i : ℕ} (hr : 1 ≤ r) (hrp : r < p)
    (hi : Eligible m p i) (hs : 2*i=m+p-i)
    {z : ℝ} (hz : 0 < z) (J : Finset ℕ)
    (hJ : ∀j∈J,Eligible m p j) (hne : ∀j∈J,i≠j)
    (horder : ∀j∈J,¬Arrow m r p i j)
    : LocalWeights.epsilon z*(∑ x, if Good m r p J x then ∏ v, z^(x v).val else 0) ≤
      ∑ x, if Good m r p J x ∧ Failure (KunzWord.coord (boundedWord x)) i
        then ∏ v, z^(x v).val else 0 := by
  let e := equiv3 hr hrp hi (Or.inr hs)
  have hc : physical (e 0).val=i := by norm_num [e,equiv3_physical,label3]
  have ht : physical (e 2).val=2*i := by
    norm_num [e,equiv3_physical,label3,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail]
    omega
  apply nonpostponed_model hr hrp hi e 0 2 hc ht z (LocalWeights.epsilon z) (le_of_lt hz) (le_of_lt (LocalWeights.epsilon_pos hz)) J hJ hne horder allowedThree failureThreeRight
  · intro b a ha
    exact GadgetSourceBounds.allowed_three hr hrp hi (Or.inr hs) a b ha
  · intro a ha
    rcases ha with ⟨h0,ht,hl⟩
    refine ⟨h0,ht,?_⟩
    intro k hk
    fin_cases k <;> simp_all [letter]
  · exact three_right_density hz

theorem postponed_four {m r p i : ℕ} (hr : 1 ≤ r) (hrp : r < p)
    (hi : Eligible m p i) (hnr : 2*i ≠ m+r-i) (hnp : 2*i ≠ m+p-i)
    {z : ℝ} (hz : 0 < z) (J : Finset ℕ)
    (hJ : ∀j∈J,Eligible m p j) (hne : ∀j∈J,i≠j)
    : LocalWeights.delta z*(∑ x, if Good m r p J x then ∏ v, z^(x v).val else 0) ≤
      ∑ x, if Good m r p J x ∧ Failure (KunzWord.coord (boundedWord x)) i
        then ∏ v, z^(x v).val else 0 := by
  let e := equiv4 hr hrp hi hnr hnp
  have hc : physical (e 0).val=i := by norm_num [e,equiv4_physical,label4]
  have ht : physical (e 1).val=2*i := by
    norm_num [e,equiv4_physical,label4,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail]
  have hl1 : physical (e 2).val=m+r-i := by norm_num [e,equiv4_physical,label4,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail]
  have hl2 : physical (e 3).val=m+p-i := by norm_num [e,equiv4_physical,label4,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail]
  apply postponed_model hr hrp hi e 0 1 2 3 hc ht hl1 hl2 z (LocalWeights.delta z) (le_of_lt hz) (le_of_lt (LocalWeights.delta_pos hz)) J hJ hne allowedFour postponedFour
  · intro b a ha
    exact GadgetSourceBounds.allowed_four hr hrp hi hnr hnp a b ha
  · intro a ha
    subst a
    norm_num [Fin.forall_fin_succ,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail]
  · exact postponed_four_density hz

theorem postponed_left {m r p i : ℕ} (hr : 1 ≤ r) (hrp : r < p)
    (hi : Eligible m p i) (hs : 2*i=m+r-i)
    {z : ℝ} (hz : 0 < z) (J : Finset ℕ)
    (hJ : ∀j∈J,Eligible m p j) (hne : ∀j∈J,i≠j)
    : LocalWeights.delta z*(∑ x, if Good m r p J x then ∏ v, z^(x v).val else 0) ≤
      ∑ x, if Good m r p J x ∧ Failure (KunzWord.coord (boundedWord x)) i
        then ∏ v, z^(x v).val else 0 := by
  let e := equiv3 hr hrp hi (Or.inl hs)
  have hc : physical (e 0).val=i := by norm_num [e,equiv3_physical,label3]
  have ht : physical (e 1).val=2*i := by
    norm_num [e,equiv3_physical,label3,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail]
    omega
  have hl1 : physical (e 1).val=m+r-i := by norm_num [e,equiv3_physical,label3,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail]
  have hl2 : physical (e 2).val=m+p-i := by norm_num [e,equiv3_physical,label3,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail]
  apply postponed_model hr hrp hi e 0 1 1 2 hc ht hl1 hl2 z (LocalWeights.delta z) (le_of_lt hz) (le_of_lt (LocalWeights.delta_pos hz)) J hJ hne allowedThree postponedThreeLeft
  · intro b a ha
    exact GadgetSourceBounds.allowed_three hr hrp hi (Or.inl hs) a b ha
  · intro a ha
    subst a
    norm_num [Fin.forall_fin_succ,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail]
  · exact postponed_three_left_density hz

theorem postponed_right {m r p i : ℕ} (hr : 1 ≤ r) (hrp : r < p)
    (hi : Eligible m p i) (hs : 2*i=m+p-i)
    {z : ℝ} (hz : 0 < z) (J : Finset ℕ)
    (hJ : ∀j∈J,Eligible m p j) (hne : ∀j∈J,i≠j)
    : LocalWeights.delta z*(∑ x, if Good m r p J x then ∏ v, z^(x v).val else 0) ≤
      ∑ x, if Good m r p J x ∧ Failure (KunzWord.coord (boundedWord x)) i
        then ∏ v, z^(x v).val else 0 := by
  let e := equiv3 hr hrp hi (Or.inr hs)
  have hc : physical (e 0).val=i := by norm_num [e,equiv3_physical,label3]
  have ht : physical (e 2).val=2*i := by
    norm_num [e,equiv3_physical,label3,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail]
    omega
  have hl1 : physical (e 1).val=m+r-i := by norm_num [e,equiv3_physical,label3,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail]
  have hl2 : physical (e 2).val=m+p-i := by norm_num [e,equiv3_physical,label3,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail]
  apply postponed_model hr hrp hi e 0 2 1 2 hc ht hl1 hl2 z (LocalWeights.delta z) (le_of_lt hz) (le_of_lt (LocalWeights.delta_pos hz)) J hJ hne allowedThree postponedThreeRight
  · intro b a ha
    exact GadgetSourceBounds.allowed_three hr hrp hi (Or.inr hs) a b ha
  · intro a ha
    subst a
    norm_num [Fin.forall_fin_succ,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail]
  · exact postponed_three_right_density hz

theorem nonpostponed {m r p i : ℕ} (hr : 1 ≤ r) (hrp : r < p)
    (hi : Eligible m p i) {z : ℝ} (hz : 0 < z) (J : Finset ℕ)
    (hJ : ∀j∈J,Eligible m p j) (hne : ∀j∈J,i≠j)
    (horder : ∀j∈J,¬Arrow m r p i j)
    : LocalWeights.epsilon z*(∑ x, if Good m r p J x then ∏ v, z^(x v).val else 0) ≤
      ∑ x, if Good m r p J x ∧ Failure (KunzWord.coord (boundedWord x)) i
        then ∏ v, z^(x v).val else 0 := by
  by_cases hl : 2*i=m+r-i
  · exact nonpostponed_left hr hrp hi hl hz J hJ hne horder
  by_cases hr' : 2*i=m+p-i
  · exact nonpostponed_right hr hrp hi hr' hz J hJ hne horder
  exact nonpostponed_four hr hrp hi hl hr' hz J hJ hne horder

theorem postponed {m r p i : ℕ} (hr : 1 ≤ r) (hrp : r < p)
    (hi : Eligible m p i) {z : ℝ} (hz : 0 < z) (J : Finset ℕ)
    (hJ : ∀j∈J,Eligible m p j) (hne : ∀j∈J,i≠j)
    : LocalWeights.delta z*(∑ x, if Good m r p J x then ∏ v, z^(x v).val else 0) ≤
      ∑ x, if Good m r p J x ∧ Failure (KunzWord.coord (boundedWord x)) i
        then ∏ v, z^(x v).val else 0 := by
  by_cases hl : 2*i=m+r-i
  · exact postponed_left hr hrp hi hl hz J hJ hne
  by_cases hr' : 2*i=m+p-i
  · exact postponed_right hr hrp hi hr' hz J hJ hne
  exact postponed_four hr hrp hi hl hr' hz J hJ hne

end
end SubmittedGenus.CapFourMass.ActualConditionalDensity
