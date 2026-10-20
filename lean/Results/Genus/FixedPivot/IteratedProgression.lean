import Results.Genus.FixedPivot.TailProgression

/-! Source component phases and lengths at every multiplicity m+kd, including k=0. -/
namespace SubmittedGenus.FixedPivot
section Progression
variable (N d : ℕ) (hN : d<N)

lemma portPartner_congr {M : ℕ} (hM : d<M) (he : N=M) :
    portPartner N d hN=portPartner M d hM := by subst M; rfl

lemma pairForPort_n_congr {M : ℕ} (hM : d<M) (he : N=M) (a : Fin d) :
    (pairForPort N d hN a).n=(pairForPort M d hM a).n := by subst M; rfl

lemma portPartner_iterated (k : ℕ) :
    portPartner (N+k*d) d (by omega)=portPartner N d hN := by
  induction k with
  | zero => exact portPartner_congr _ d _ hN (by omega)
  | succ k ih =>
    calc
      _ = portPartner ((N+k*d)+d) d (by omega) :=
        portPartner_congr _ d _ _ (by ring)
      _ = portPartner (N+k*d) d (by omega) := portPartner_progression (N+k*d) d (by omega)
      _ = _ := ih

lemma pairForPort_iterated (k : ℕ) (a : Fin d) :
    (pairForPort (N+k*d) d (by omega) a).n=(pairForPort N d hN a).n+k := by
  induction k with
  | zero => exact pairForPort_n_congr _ d _ hN (by omega) a
  | succ k ih =>
    calc
      _ = (pairForPort ((N+k*d)+d) d (by omega) a).n :=
        pairForPort_n_congr _ d _ _ (by ring) a
      _ = (pairForPort (N+k*d) d (by omega) a).n+1 :=
        (pairForPort_progression (N+k*d) d (by omega) a).2
      _ = _ := by rw [ih]; omega

def carryRepresentativeIterated (k : ℕ) :
    CarryRepresentative N d hN ≃ CarryRepresentative (N+k*d) d (by omega) where
  toFun a:=⟨a.val,by rw [portPartner_iterated]; exact a.property⟩
  invFun a:=⟨a.val,by rw [← portPartner_iterated N d hN k]; exact a.property⟩
  left_inv a:=rfl
  right_inv a:=rfl

lemma carryRepresentativeIterated_val (k : ℕ) (a : CarryRepresentative N d hN) :
    (carryRepresentativeIterated N d hN k a).val=a.val := rfl

lemma componentPair_iterated (k : ℕ) (a : CarryRepresentative N d hN) :
    (componentPair (N+k*d) d (by omega) (carryRepresentativeIterated N d hN k a)).n=
      (componentPair N d hN a).n+k := pairForPort_iterated N d hN k a.val

lemma carryTailSize_iterated (k : ℕ) (a : CarryRepresentative N d hN) :
    carryTailSize (N+k*d) d (by omega) (carryRepresentativeIterated N d hN k a)=
      carryTailSize N d hN a+carryPortArity N d hN a*k := by
  have hn:=(componentPair N d hN a).n_pos
  unfold carryTailSize carryComponentSize carryPortArity
  rw [carryRepresentativeIterated_val,portPartner_iterated N d hN,
    componentPair_iterated N d hN]
  split_ifs <;> omega

/-- The actual number of transfer edges has the exact claimed arity increment. -/
theorem carryTailEdges_iterated (hbig : 2*d<N) (k : ℕ) (a : CarryRepresentative N d hN) :
    carryTailSize (N+k*d) d (by omega) (carryRepresentativeIterated N d hN k a)-1=
      (carryTailSize N d hN a-1)+carryPortArity N d hN a*k := by
  rw [carryTailSize_iterated]
  have hn:=carryTailSize_positive N d hN hbig a
  omega

end Progression
end SubmittedGenus.FixedPivot
