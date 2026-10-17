import Results.Genus.CapFourMass.GadgetFibers

namespace SubmittedGenus.CapFourMass.GadgetSourceBounds
open RawGraph RawGraph.SourceModel ContractionGeometry GadgetCoordinates GadgetFibers

lemma high_alphabet {m r p : ℕ} {x : Word m} (hx : Admissible r p 4 x)
    (v : Fin (m-1)) (hv : p < physical v) : 1 ≤ x v ∧ x v ≤ 3 := by
  have hrp := hx.1.2.1
  have hfree : IsFree r p v := by unfold IsFree IsPivot; omega
  have hh := (hx.2.1 v).2 hfree
  have hup : upper r 4 v = 3 := by unfold upper; split_ifs <;> omega
  exact ⟨domain_positive v (hx.2.1 v),by simpa [hup] using hh.2⟩

lemma carried_pair {m r p : ℕ} {x : Word m} (hx : Admissible r p 4 x)
    (u v : Fin (m-1)) (hu : p < physical u) (hv : p < physical v)
    (hc : physical u+physical v=m+r ∨ physical u+physical v=m+p) :
    3 ≤ x u+x v := by
  have hrp := hx.1.2.1
  have hfu : IsFree r p u := by unfold IsFree IsPivot; omega
  have hfv : IsFree r p v := by unfold IsFree IsPivot; omega
  by_cases he : u=v
  · subst v
    have hd := (domain_iff_unary u (x u)).mp (hx.2.1 u)
    have hl : CarryLoop r p u := by unfold CarryLoop; omega
    have hh := (hd.2 hfu).2.2.2 hl
    omega
  · have hh := LayoutCompiler.admissible_edge_all hx u v
    have hzero : ¬(IsPivot r p u ∨ IsPivot r p v ∨ u=v) := by tauto
    have hstrong : ¬(physical u+physical v=r ∨ physical u+physical v=p) := by omega
    simpa [edgeBound,hzero,hstrong,hc] using hh

lemma alphabet_reindexed {m r p i n : ℕ}
    (hr : 1 ≤ r) (hrp : r < p) (hi : Eligible m p i)
    (e : Fin n ≃ PhysicalVertices m r p i) (a : Fin n → Fin 5)
    (b : Outside m r p i) (hx : Admissible r p 4 (naturalWord e a b)) :
    GadgetLocalSums.alphabet a := by
  intro k
  have hh := high_alphabet hx (e k).val (gadget_high hr hrp hi (e k).property)
  simpa only [natural_inside,GadgetLocalSums.letter] using hh

lemma allowed_four {m r p i : ℕ} (hr : 1 ≤ r) (hrp : r < p)
    (hi : Eligible m p i) (hnr : 2*i ≠ m+r-i) (hnp : 2*i ≠ m+p-i)
    (a : Fin 4 → Fin 5) (b : Outside m r p i)
    (hx : Admissible r p 4 (naturalWord (equiv4 hr hrp hi hnr hnp) a b)) :
    GadgetLocalSums.allowedFour a := by
  let e := equiv4 hr hrp hi hnr hnp
  have hg := gadget_bounds hr hrp hi
  refine ⟨alphabet_reindexed hr hrp hi e a b hx, ?_, ?_⟩
  · have hh := carried_pair hx (e 0).val (e 2).val
      (gadget_high hr hrp hi (e 0).property) (gadget_high hr hrp hi (e 2).property) ?_
    · simpa only [e,natural_inside,GadgetLocalSums.letter] using hh
    · left
      norm_num [e,equiv4_physical,label4,Matrix.cons_val_zero,Matrix.cons_val_two,
        Matrix.vecHead,Matrix.vecTail,Matrix.cons_val_one]
      omega
  · have hh := carried_pair hx (e 0).val (e 3).val
      (gadget_high hr hrp hi (e 0).property) (gadget_high hr hrp hi (e 3).property) ?_
    · simpa only [e,natural_inside,GadgetLocalSums.letter] using hh
    · right
      norm_num [e,equiv4_physical,label4,Matrix.cons_val_zero,Matrix.cons_val_three,Matrix.cons_val_two,
        Matrix.vecHead,Matrix.vecTail,Matrix.cons_val_one]
      omega

lemma allowed_three {m r p i : ℕ} (hr : 1 ≤ r) (hrp : r < p)
    (hi : Eligible m p i) (hshared : 2*i=m+r-i ∨ 2*i=m+p-i)
    (a : Fin 3 → Fin 5) (b : Outside m r p i)
    (hx : Admissible r p 4 (naturalWord (equiv3 hr hrp hi hshared) a b)) :
    GadgetLocalSums.allowedThree a := by
  let e := equiv3 hr hrp hi hshared
  have hg := gadget_bounds hr hrp hi
  refine ⟨alphabet_reindexed hr hrp hi e a b hx, ?_, ?_⟩
  · have hh := carried_pair hx (e 0).val (e 1).val
      (gadget_high hr hrp hi (e 0).property) (gadget_high hr hrp hi (e 1).property) ?_
    · simpa only [e,natural_inside,GadgetLocalSums.letter] using hh
    · left
      norm_num [e,equiv3_physical,label3,Matrix.cons_val_zero,Matrix.cons_val_one]
      omega
  · have hh := carried_pair hx (e 0).val (e 2).val
      (gadget_high hr hrp hi (e 0).property) (gadget_high hr hrp hi (e 2).property) ?_
    · simpa only [e,natural_inside,GadgetLocalSums.letter] using hh
    · right
      norm_num [e,equiv3_physical,label3,Matrix.cons_val_zero,Matrix.cons_val_two,
        Matrix.vecHead,Matrix.vecTail,Matrix.cons_val_one]
      omega

end SubmittedGenus.CapFourMass.GadgetSourceBounds
