import Results.Genus.FixedPivot.CanonicalSource
import Results.Genus.FixedPivot.EndpointModes
import Results.Genus.FixedPivot.PureProduct

/-! Pairing-independent pure-mode factors of the actual canonical core contraction. -/
namespace SubmittedGenus.FixedPivot
open scoped BigOperators
noncomputable section

/-- A total port-state function; invalid core assignments are killed by stableCoreTerm. -/
def canonicalPortState {r d : ℕ} (x : Fin (r+d)→Fin 5) (a : Fin d) : Fin 3 :=
  ⟨((x (canonicalPortIndex r d a)).val-1)%3,Nat.mod_lt _ (by omega)⟩

lemma canonical_port_color {r d : ℕ} (x : Fin (r+d)→Fin 5) (hx : StableCoreAllowed r (r+d) x)
    (a : Fin d) (ha : a.val+1≠d) :
    1≤(x (canonicalPortIndex r d a)).val ∧ (x (canonicalPortIndex r d a)).val≤3 := by
  have hh:=(hx.1) (canonicalPortIndex r d a)
  unfold CoreDomain canonicalPortIndex at hh
  dsimp only at hh
  have hb:=a.isLt
  have hc:=hh.2 (by omega)
  rw [if_neg (by omega)] at hc
  exact ⟨hc.1,hc.2.1⟩

lemma canonicalPortState_value {r d : ℕ} (x : Fin (r+d)→Fin 5)
    (hx : StableCoreAllowed r (r+d) x) (a : Fin d) (ha : a.val+1≠d) :
    (canonicalPortState x a).val+1=(x (canonicalPortIndex r d a)).val := by
  have hh:=canonical_port_color x hx a ha
  unfold canonicalPortState
  dsimp only
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

def pivotPort (d : ℕ) (hd : 0<d) : Fin d := ⟨d-1,by omega⟩

lemma eq_pivotPort_iff {d : ℕ} (hd : 0<d) (a : Fin d) :
    a=pivotPort d hd ↔ a.val+1=d := by
  rw [Fin.ext_iff]
  unfold pivotPort
  dsimp only
  have ha:=a.isLt
  omega

section Ring
variable {R : Type*} [CommRing R]

lemma canonical_port_endpoint (z theta other : R)
    (hb : theta+other=carryB z) (hc : theta*other=carryC z)
    {r d : ℕ} (hd : 0<d) (x : Fin (r+d)→Fin 5) (hx : StableCoreAllowed r (r+d) x)
    (a : Fin d) :
    carryWeightedDot z theta (fun v : Fin 3 => if canonicalPortAllowed x a (v.val+1) then 1 else 0)=
      if a=pivotPort d hd then carryB z*(z+theta)
      else theta*carryEigenvector z theta (canonicalPortState x a) := by
  by_cases ha : a.val+1=d
  · rw [if_pos ((eq_pivotPort_iff hd a).2 ha)]
    have hg : (fun v : Fin 3 => if canonicalPortAllowed x a (v.val+1) then (1 : R) else 0)=freeTerminal := by
      funext v
      simp only [canonicalPortAllowed,ha,true_or,ite_true]
      exact (freeTerminal_loop_free v).symm
    rw [hg,free_endpoint_factor]
  · rw [if_neg (fun h => ha ((eq_pivotPort_iff hd a).1 h))]
    have hg : (fun v : Fin 3 => if canonicalPortAllowed x a (v.val+1) then (1 : R) else 0)=
        fun v => carryCompatibility (canonicalPortState x a) v := by
      funext v
      unfold canonicalPortAllowed carryCompatibility
      rw [canonicalPortState_value x hx a ha]
      simp only [ha,false_or]
    rw [hg,port_endpoint_factor z theta other hb hc]

lemma canonical_start_endpoint (z theta other : R)
    (hb : theta+other=carryB z) (hc : theta*other=carryC z)
    {r N d : ℕ} (hd : 0<d) {hN : d<N} (x : Fin (r+d)→Fin 5)
    (hx : StableCoreAllowed r (r+d) x) (c : CarryRepresentative N d hN) :
    carryWeightedDot z theta (fun v => if canonicalStartAllowed x c v then 1 else 0)=
      if c.val=pivotPort d hd then carryB z*(z+theta)
      else theta*carryEigenvector z theta (canonicalPortState x c.val) :=
  canonical_port_endpoint z theta other hb hc hd x hx c.val

lemma canonical_finish_endpoint (z theta other : R)
    (hb : theta+other=carryB z) (hc : theta*other=carryC z)
    {r N d : ℕ} (hd : 0<d) {hN : d<N} (x : Fin (r+d)→Fin 5)
    (hx : StableCoreAllowed r (r+d) x) (c : CarryRepresentative N d hN) :
    carryWeightedDot z theta (fun v => if canonicalFinishAllowed x c v then 1 else 0)=
      if c.val=portPartner N d hN c.val then carryB z*theta else
        if portPartner N d hN c.val=pivotPort d hd then carryB z*(z+theta)
        else theta*carryEigenvector z theta (canonicalPortState x (portPartner N d hN c.val)) := by
  by_cases hf : c.val=portPartner N d hN c.val
  · rw [if_pos hf]
    have hg : (fun v : Fin 3 => if canonicalFinishAllowed x c v then (1 : R) else 0)=loopTerminal := by
      funext v
      simp only [canonicalFinishAllowed,if_pos hf]
      fin_cases v <;> rfl
    rw [hg,loop_endpoint_factor]
  · rw [if_neg hf]
    simp only [canonicalFinishAllowed,if_neg hf]
    exact canonical_port_endpoint z theta other hb hc hd x hx _

/-- The exact pure component product is independent of every port pairing. -/
theorem canonical_pure_component_product (z theta other bi ti di : R)
    (hb : theta+other=carryB z) (hc : theta*other=carryC z) (hbi : carryB z*bi=1)
    {r N d : ℕ} (hd : 0<d) (hN : d<N) (hbig : 2*d<N)
    (x : Fin (r+d)→Fin 5) (hx : StableCoreAllowed r (r+d) x) :
    (∏ c : CarryRepresentative N d hN,
      weightedModeAmplitude z theta other ti di (carryTailSize N d hN c-1)
        (fun v => if canonicalStartAllowed x c v then 1 else 0)
        (fun v => if canonicalFinishAllowed x c v then 1 else 0))=
      theta^(carrySourceEdgeCount N d)*(bi*ti*di)^(Fintype.card (CarryRepresentative N d hN))*
      (carryB z*(z+theta))*(carryB z*theta)^(carryFixedCount N d hN)*
      (∏ a ∈ Finset.univ.erase (pivotPort d hd),carryEigenvector z theta (canonicalPortState x a)) := by
  exact pure_component_product_with_pivot N d hd hN hbig z theta other bi ti di hb hc hbi
    _ _ (pivotPort d hd) (fun a => carryEigenvector z theta (canonicalPortState x a))
    _ _ (canonical_start_endpoint z theta other hb hc hd x hx)
    (canonical_finish_endpoint z theta other hb hc hd x hx)

end Ring
end
end SubmittedGenus.FixedPivot
