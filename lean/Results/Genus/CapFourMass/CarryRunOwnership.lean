import Results.Genus.CapFourMass.FreeCarryVertices

/-! Maximality and actual component ownership of every canonical carry run. -/
noncomputable section
namespace SubmittedGenus.CapFourMass.CarryLocalization
open RawGraph RawGraph.SourceModel RawGraph.Topology FixedPivot

section Ownership
variable {r N d : ℕ} (hr : 0<r) (hd : 0<d) (hN : d<N) (hbig : 2*d<N)

include hd hbig in
/-- A canonical retained carry run is connected in the actual raw graph. -/
lemma run_same_component (a : CarryRepresentative N d hN)
    (t s : Fin (freeCarrySize N d hN a)) :
    (freeGraph (r+N) r (r+d)).connectedComponentMk (runVertex hr hN a t)=
      (freeGraph (r+N) r (r+d)).connectedComponentMk (runVertex hr hN a s) := by
  have hn:=freeCarrySize_positive N d hN hbig a
  have haux : ∀k (hk : k<freeCarrySize N d hN a),
      (freeGraph (r+N) r (r+d)).connectedComponentMk (runVertex hr hN a ⟨k,hk⟩)=
        (freeGraph (r+N) r (r+d)).connectedComponentMk (runVertex hr hN a ⟨0,hn⟩) := by
    intro k
    induction k with
    | zero => intro hk; rfl
    | succ k ih =>
      intro hk
      have hk' : k<freeCarrySize N d hN a := by omega
      have ha:=(run_carry_adj_iff hr hd hN a ⟨k,hk'⟩ ⟨k+1,hk⟩).mpr (Or.inl rfl)
      exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj ha.adj).symm.trans (ih hk')
  exact (haux t.val t.isLt).trans (haux s.val s.isLt).symm

include hd in
/-- The retained run and the conditioned tail use the same actual component
key, so no orientation choice enters complete-mode regrouping. -/
theorem run_owner (a : CarryRepresentative N d hN) (t : Fin (freeCarrySize N d hN a)) :
    (freeGraph (r+N) r (r+d)).connectedComponentMk (runVertex hr hN a t)=
      owner hr hN hbig a := by
  have hp:=deletedPrefix_le_one N d hN a
  have hn:=componentSize_two N d hN hbig a
  let s : Fin (freeCarrySize N d hN a):=⟨1-deletedPrefix N d hN a,by
    unfold freeCarrySize
    omega⟩
  let z : Fin (carryTailSize N d hN a):=⟨0,carryTailSize_positive N d hN hbig a⟩
  have he : runVertex hr hN a s=tailVertex hr hN a z := by
    apply Subtype.ext
    apply Fin.ext
    change r+carryComponentLabel N d hN a (1-deletedPrefix N d hN a+deletedPrefix N d hN a)-1=
      r+carryComponentLabel N d hN a (0+1)-1
    rw [Nat.sub_add_cancel hp]
  exact (run_same_component hr hd hN hbig a t s).trans
    ((congrArg (freeGraph (r+N) r (r+d)).connectedComponentMk he).trans (tail_owner hr hN hbig a z))

/-- Internal canonical carry-run vertices lie outside the original finite core. -/
lemma run_internal_gt_p (a : CarryRepresentative N d hN) (t : Fin (freeCarrySize N d hN a))
    (hfirst : 0<t.val) (hlast : t.val+1<freeCarrySize N d hN a) :
    r+d<physical (runVertex hr hN a t).val := by
  rw [runVertex_physical]
  have hh:=freeCarry_internal_gt N d hN a t.isLt hfirst hlast
  omega

include hd in
/-- No strong edge can interrupt the interior of a canonical carry run. -/
lemma run_strong_endpoint (a : CarryRepresentative N d hN) (t : Fin (freeCarrySize N d hN a))
    {v : Fin (r+N-1)}
    (hs : StrongRuns.StrongStep r (r+d) (runVertex hr hN a t).val v) :
    t.val=0 ∨ t.val+1=freeCarrySize N d hN a := by
  have hp:=StrongRuns.strong_endpoint_lt_p (canonicalParameters hr hd hN) hs
  rw [runVertex_physical] at hp
  have hh:=freeCarry_port_iff N d hN a t.isLt
  have ht:=t.isLt
  omega

/-- The retained unary carry loop agrees with the original physical source. -/
lemma run_carry_loop_iff (a : CarryRepresentative N d hN) (t : Fin (freeCarrySize N d hN a)) :
    CarryLoop r (r+d) (runVertex hr hN a t).val ↔
      a.val=portPartner N d hN a.val ∧ t.val=freeCarrySize N d hN a-1 := by
  have hh:=freeCarry_loop_iff N d hN a t.isLt
  unfold CarryLoop
  rw [runVertex_physical]
  omega

end Ownership
end SubmittedGenus.CapFourMass.CarryLocalization
