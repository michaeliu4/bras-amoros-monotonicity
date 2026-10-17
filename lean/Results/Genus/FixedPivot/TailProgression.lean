import Results.Genus.FixedPivot.Progression
import Results.Genus.FixedPivot.TailLayout

/-! The trimmed physical carry tails retain the exact source progression increments. -/
namespace SubmittedGenus.FixedPivot
section Progression
variable (N d : ℕ) (hN : d<N)

lemma carryPortArity_progression (a : CarryRepresentative N d hN) :
    carryPortArity (N+d) d (by omega) (carryRepresentativeProgression N d hN a)=
      carryPortArity N d hN a := by
  unfold carryPortArity
  rw [carryRepresentativeProgression_val,portPartner_progression N d hN]

theorem carryTailSize_progression (a : CarryRepresentative N d hN) :
    carryTailSize (N+d) d (by omega) (carryRepresentativeProgression N d hN a)=
      carryTailSize N d hN a+carryPortArity N d hN a := by
  unfold carryTailSize
  rw [carryComponentSize_progression,carryPortArity_progression]
  have hn:=(componentPair N d hN a).n_pos
  unfold carryComponentSize carryPortArity
  split_ifs <;> omega

theorem carryTailEdges_progression (hbig : 2*d<N) (a : CarryRepresentative N d hN) :
    carryTailSize (N+d) d (by omega) (carryRepresentativeProgression N d hN a)-1=
      (carryTailSize N d hN a-1)+carryPortArity N d hN a := by
  rw [carryTailSize_progression]
  have hpos:=carryTailSize_positive N d hN hbig a
  omega

/-- The paired tail kernel always has positive edge length; only fixed classes
can contain the zero-edge free-to-loop source. -/
theorem carryTailEdges_positive_paired (hbig : 2*d<N) (a : CarryRepresentative N d hN)
    (hf : a.val≠portPartner N d hN a.val) : 0<carryTailSize N d hN a-1 := by
  have hn:=componentPair_two N d hN hbig a
  unfold carryTailSize carryComponentSize carryPortArity
  simp only [if_neg hf]
  omega

end Progression
end SubmittedGenus.FixedPivot
