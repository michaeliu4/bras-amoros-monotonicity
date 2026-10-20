import Results.Genus.FixedPivot.KernelModes
import Results.Genus.FixedPivot.ConditionedTransfer
import Results.Genus.FixedPivot.CoreSource

/-! Actual core port gates have the eigenvector endpoint factors used in pure-mode cancellation. -/
namespace SubmittedGenus.FixedPivot
open RawGraph
open scoped BigOperators
section Ring
variable {R : Type*} [CommRing R]

/-- A fixed source port contributes theta times one eigenvector entry. -/
theorem port_endpoint_factor (z theta other : R)
    (hb : theta+other=carryB z) (hc : theta*other=carryC z) (port : Fin 3) :
    carryWeightedDot z theta (fun v => carryCompatibility port v)=theta*carryEigenvector z theta port := by
  have hh:=congrFun (carryEigenvector_eigen z theta other hb hc) port
  rw [carryStep_eq_sum] at hh
  calc
    _ = ∑ v : Fin 3,carryCompatibility port v*carryWeight z v*carryEigenvector z theta v := by
      unfold carryWeightedDot carryEndpointWeight
      apply Finset.sum_congr rfl
      intro v _
      ring
    _ = _ := hh

end Ring
noncomputable section Source
variable {m r p : ℕ} (hp : Parameters m r p 4)

lemma stable_core_port_color (x : Fin p→Fin 5) (hx : StableCoreAllowed r p x)
    (a : Fin (p-r)) (ha : a.val+1≠p-r) :
    1≤(x (conditionedPortIndex hp a)).val ∧ (x (conditionedPortIndex hp a)).val≤3 := by
  have hh:=(hx.1) (conditionedPortIndex hp a)
  unfold CoreDomain at hh
  have ha':=a.isLt
  have hrp:=hp.2.1
  have hfree : ¬((conditionedPortIndex hp a).val+1=r ∨ (conditionedPortIndex hp a).val+1=p) := by
    rw [conditionedPortIndex_val]
    omega
  have hc:=hh.2 hfree
  rw [conditionedPortIndex_val,if_neg (by omega)] at hc
  exact ⟨hc.1,hc.2.1⟩

def stablePortColor (x : Fin p→Fin 5) (hx : StableCoreAllowed r p x)
    (a : Fin (p-r)) (ha : a.val+1≠p-r) : Fin 3 :=
  ⟨(x (conditionedPortIndex hp a)).val-1,by
    have hh:=stable_core_port_color hp x hx a ha
    omega⟩

lemma stablePortColor_value (x : Fin p→Fin 5) (hx : StableCoreAllowed r p x)
    (a : Fin (p-r)) (ha : a.val+1≠p-r) :
    (stablePortColor hp x hx a ha).val+1=(x (conditionedPortIndex hp a)).val := by
  have hh:=stable_core_port_color hp x hx a ha
  unfold stablePortColor
  dsimp only
  omega

lemma sourcePortAllowed_pivot (x : Fin p→Fin 5) (a : Fin (p-r)) (ha : a.val+1=p-r) (v : ℕ) :
    sourcePortAllowed hp x a v := Or.inl ha

lemma sourcePort_gate_eq_compatibility {R : Type*} [CommRing R]
    (x : Fin p→Fin 5) (hx : StableCoreAllowed r p x)
    (a : Fin (p-r)) (ha : a.val+1≠p-r) (v : Fin 3) :
    (if sourcePortAllowed hp x a (v.val+1) then 1 else 0 : R)=
      carryCompatibility (stablePortColor hp x hx a ha) v := by
  unfold sourcePortAllowed carryCompatibility
  rw [stablePortColor_value]
  simp only [ha,false_or]

/-- Every actual surviving port has precisely its rational rank-one endpoint factor. -/
theorem source_port_endpoint_factor {R : Type*} [CommRing R] (z theta other : R)
    (hb : theta+other=carryB z) (hc : theta*other=carryC z)
    (x : Fin p→Fin 5) (hx : StableCoreAllowed r p x)
    (a : Fin (p-r)) (ha : a.val+1≠p-r) :
    carryWeightedDot z theta (fun v => if sourcePortAllowed hp x a (v.val+1) then 1 else 0)=
      theta*carryEigenvector z theta (stablePortColor hp x hx a ha) := by
  have he : (fun v : Fin 3 => if sourcePortAllowed hp x a (v.val+1) then (1 : R) else 0)=
      fun v => carryCompatibility (stablePortColor hp x hx a ha) v := by
    funext v
    exact sourcePort_gate_eq_compatibility hp x hx a ha v
  rw [he]
  exact port_endpoint_factor z theta other hb hc _

end Source
end SubmittedGenus.FixedPivot
