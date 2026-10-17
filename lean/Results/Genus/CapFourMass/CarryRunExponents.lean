import Results.Genus.CapFourMass.FreeCarryLayout

/-! Canonical tail edges and surviving port edges give exactly the retained
physical carry-run exponent, including deletion of the pivot endpoint. -/
namespace SubmittedGenus.CapFourMass.CarryLocalization
open FixedPivot

lemma freeCarry_edge_count (N d : ℕ) (hN : d<N) (hbig : 2*d<N)
    (a : CarryRepresentative N d hN) :
    freeCarrySize N d hN a-1=
      (carryTailSize N d hN a-1)+(carryPortArity N d hN a-deletedPrefix N d hN a) := by
  have ht:=carryTailSize_positive N d hN hbig a
  have hp:=carryPortArity_pos N d hN a
  have hd:=deletedPrefix_le_one N d hN a
  unfold freeCarrySize carryTailSize at *
  omega

lemma freeCarry_mode_power {R : Type*} [Monoid R] (N d : ℕ) (hN : d<N) (hbig : 2*d<N)
    (a : CarryRepresentative N d hN) (z : R) :
    z^(freeCarrySize N d hN a-1)=z^(carryTailSize N d hN a-1)*
      z^(carryPortArity N d hN a-deletedPrefix N d hN a) := by
  rw [freeCarry_edge_count N d hN hbig a,pow_add]

lemma survivingPorts_fixed (N d : ℕ) (hN : d<N) (a : CarryRepresentative N d hN)
    (hf : a.val=portPartner N d hN a.val) :
    carryPortArity N d hN a-deletedPrefix N d hN a=
      if a.val.val+1=d then 0 else 1 := by
  rw [carryPortArity,if_pos hf]
  unfold deletedPrefix
  split_ifs <;> omega

lemma survivingPorts_paired (N d : ℕ) (hN : d<N) (a : CarryRepresentative N d hN)
    (hf : a.val≠portPartner N d hN a.val) :
    carryPortArity N d hN a-deletedPrefix N d hN a=
      if a.val.val+1=d then 1 else 2 := by
  rw [carryPortArity,if_neg hf]
  unfold deletedPrefix
  split_ifs <;> omega

end SubmittedGenus.CapFourMass.CarryLocalization
