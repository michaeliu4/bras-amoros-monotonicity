import Results.Genus.CapFourMass.RetainedModeRun
import Results.Genus.CapFourMass.PhysicalModeWeights

/-! Actual local core-port factors regroup by the proved carry endpoint
bijection. Each retained mode keeps both of its own endpoints before any
absolute value or core assignment sum is taken. -/
noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.CapFourMass.SourceCoreFactorization
open RawGraph RawGraph.SourceModel RawGraph.Topology FixedPivot CarryLocalization
attribute [local instance] Classical.propDecidable Classical.decEq
section Geometry
variable {r N d : ℕ} (hr : 0<r) (hd : 0<d) (hN : d<N) (hbig : 2*d<N)
variable (c : SourceComponent r N d)

/-- The first canonical port belongs to the same actual component as its run. -/
def firstModePort (a : ModeFiber hr hN hbig c) : PortAt hr hN hbig c :=
  ⟨a.val.val,by
    unfold portOwner
    rw [carryRepresentative_of_rep]
    exact a.property⟩

def lastModePort (a : ModeFiber hr hN hbig c) : PortAt hr hN hbig c :=
  ⟨portPartner N d hN a.val.val,by
    unfold portOwner
    rw [carryRepresentative_partner,carryRepresentative_of_rep]
    exact a.property⟩

def localPortLabel (v : Σ a : ModeFiber hr hN hbig c,Fin (carryPortArity N d hN a.val)) :
    PortAt hr hN hbig c :=
  ⟨carryPortLabel N d hN ⟨v.1.val,v.2⟩,by
    unfold portOwner
    rw [carryPortLabel_representative]
    exact v.1.property⟩

lemma localPortLabel_injective : Function.Injective (localPortLabel hr hN hbig c) := by
  rintro ⟨⟨a,ha⟩,i⟩ ⟨⟨b,hb⟩,j⟩ he
  have hh:=carryPortLabel_injective N d hN (congrArg Subtype.val he)
  change (⟨a,i⟩ : Σ a : CarryRepresentative N d hN,Fin (carryPortArity N d hN a))=⟨b,j⟩ at hh
  cases hh
  rfl

lemma localPortLabel_surjective : Function.Surjective (localPortLabel hr hN hbig c) := by
  intro q
  obtain ⟨⟨a,i⟩,he⟩:=carryPortLabel_surjective N d hN q.val
  have ha : owner hr hN hbig a=c := by
    have hh:=q.property
    unfold portOwner at hh
    rw [←he,carryPortLabel_representative] at hh
    exact hh
  exact ⟨⟨⟨a,ha⟩,i⟩,Subtype.ext he⟩

def localPortEquiv :
    (Σ a : ModeFiber hr hN hbig c,Fin (carryPortArity N d hN a.val)) ≃ PortAt hr hN hbig c :=
  Equiv.ofBijective (localPortLabel hr hN hbig c)
    ⟨localPortLabel_injective hr hN hbig c,localPortLabel_surjective hr hN hbig c⟩

lemma localPortLabel_eq (a : ModeFiber hr hN hbig c) (i : Fin (carryPortArity N d hN a.val)) :
    localPortLabel hr hN hbig c ⟨a,i⟩=
      if i.val=0 then firstModePort hr hN hbig c a else lastModePort hr hN hbig c a := by
  split_ifs with hi
  · apply Subtype.ext
    exact if_pos hi
  · apply Subtype.ext
    exact if_neg hi

lemma localPort_component_product (g : PortAt hr hN hbig c→ℝ) (a : ModeFiber hr hN hbig c) :
    (∏ i : Fin (carryPortArity N d hN a.val),g (localPortLabel hr hN hbig c ⟨a,i⟩))=
      g (firstModePort hr hN hbig c a)*
        (if a.val.val=portPartner N d hN a.val.val then 1 else g (lastModePort hr hN hbig c a)) := by
  simp_rw [localPortLabel_eq]
  by_cases hf : a.val.val=portPartner N d hN a.val.val
  · have ha : carryPortArity N d hN a.val=1 := by rw [carryPortArity,if_pos hf]
    rw [if_pos hf,mul_one]
    calc
      _ = ∏ i : Fin 1,g (if i.val=0 then firstModePort hr hN hbig c a else lastModePort hr hN hbig c a) :=
        Fintype.prod_equiv (finCongr ha) _ _ (fun _ => rfl)
      _ = _ := by simp [Fin.prod_univ_succ]
  · have ha : carryPortArity N d hN a.val=2 := by rw [carryPortArity,if_neg hf]
    rw [if_neg hf]
    calc
      _ = ∏ i : Fin 2,g (if i.val=0 then firstModePort hr hN hbig c a else lastModePort hr hN hbig c a) :=
        Fintype.prod_equiv (finCongr ha) _ _ (fun _ => rfl)
      _ = _ := by simp [Fin.prod_univ_succ]

lemma localPort_product (g : PortAt hr hN hbig c→ℝ) :
    (∏ q : PortAt hr hN hbig c,g q)=
      ∏ a : ModeFiber hr hN hbig c,g (firstModePort hr hN hbig c a)*
        (if a.val.val=portPartner N d hN a.val.val then 1 else g (lastModePort hr hN hbig c a)) := by
  have hh:=(localPortEquiv hr hN hbig c).prod_comp g
  rw [Fintype.prod_sigma] at hh
  change (∏ a : ModeFiber hr hN hbig c,∏ i : Fin (carryPortArity N d hN a.val),
    g (localPortLabel hr hN hbig c ⟨a,i⟩))=_ at hh
  simpa only [localPort_component_product] using hh.symm

/-- The arbitrary default state is used only at the deleted pivot, where the
retained boundary is free and does not read a core state. -/
def localPortState (x : CoreAt hN c→State) (q : PortAt hr hN hbig c) : State :=
  if hq : q.val.val+1=d then 0 else x (portCoreAt hr hd hN hbig q hq)

lemma firstModePort_mode (b : ModeFiber hr hN hbig c→Bool) (a : ModeFiber hr hN hbig c) :
    portModeAt hr hN hbig b (firstModePort hr hN hbig c a)=choiceMode (b a) := by
  unfold portModeAt
  congr 2
  apply Subtype.ext
  exact carryRepresentative_of_rep N d hN a.val
lemma lastModePort_mode (b : ModeFiber hr hN hbig c→Bool) (a : ModeFiber hr hN hbig c) :
    portModeAt hr hN hbig b (lastModePort hr hN hbig c a)=choiceMode (b a) := by
  unfold portModeAt
  congr 2
  apply Subtype.ext
  exact (carryRepresentative_partner N d hN a.val.val).trans (carryRepresentative_of_rep N d hN a.val)

lemma initialPortMode_eq {x : CoreAt hN c→State} (hx : componentCoreAllowed hN c x)
    (b : ModeFiber hr hN hbig c→Bool) (a : ModeFiber hr hN hbig c) :
    initialPortMode N d hN a.val (choiceMode (b a))
      (localPortState hr hd hN hbig c x (firstModePort hr hN hbig c a))=
      componentPortFactor hr hd hN hbig c x b (firstModePort hr hN hbig c a) := by
  by_cases hp : a.val.val.val+1=d
  · rw [initialPortMode,if_pos hp,componentPortFactor,
      dif_pos (show (firstModePort hr hN hbig c a).val.val+1=d from hp),firstModePort_mode]
  · rw [componentPortFactor_physical hr hd hN hbig c hx b _ hp,firstModePort_mode,
      initialPortMode,if_neg hp,localPortState,
      dif_neg (show (firstModePort hr hN hbig c a).val.val+1≠d from hp)]

lemma paired_last_not_pivot (a : ModeFiber hr hN hbig c)
    (hf : a.val.val≠portPartner N d hN a.val.val) :
    (lastModePort hr hN hbig c a).val.val+1≠d := by
  intro he
  have hle:=a.val.property
  have hi:=a.val.val.isLt
  apply hf
  apply Fin.ext
  change (portPartner N d hN a.val.val).val+1=d at he
  omega

lemma terminalPortMode_eq {x : CoreAt hN c→State} (hx : componentCoreAllowed hN c x)
    (b : ModeFiber hr hN hbig c→Bool) (a : ModeFiber hr hN hbig c) :
    terminalPortMode N d hN a.val (choiceMode (b a))
      (localPortState hr hd hN hbig c x (lastModePort hr hN hbig c a))=
      if a.val.val=portPartner N d hN a.val.val then 1
      else componentPortFactor hr hd hN hbig c x b (lastModePort hr hN hbig c a) := by
  by_cases hf : a.val.val=portPartner N d hN a.val.val
  · simp only [terminalPortMode,if_pos hf]
  · have hp:=paired_last_not_pivot hr hN hbig c a hf
    rw [if_neg hf,componentPortFactor_physical hr hd hN hbig c hx b _ hp,lastModePort_mode]
    simp only [terminalPortMode,if_neg hf,localPortState,dif_neg hp]

/-- Exact per-component signed factor regrouping before the core sum or abs. -/
theorem componentModeTerm_retained {x : CoreAt hN c→State} (hx : componentCoreAllowed hN c x)
    (b : ModeFiber hr hN hbig c→Bool) :
    componentModeTerm hr hd hN hbig c x b=componentCoreTerm hN radius c x*
      ∏ a : ModeFiber hr hN hbig c,retainedSourceMode N d hN a.val (choiceMode (b a))
        (localPortState hr hd hN hbig c x (firstModePort hr hN hbig c a))
        (localPortState hr hd hN hbig c x (lastModePort hr hN hbig c a)) := by
  unfold componentModeTerm componentCarryFactor
  rw [localPort_product hr hN hbig c]
  rw [mul_assoc,←Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro a _
  rw [retainedSourceMode,initialPortMode_eq hr hd hN hbig c hx b a,
    terminalPortMode_eq hr hd hN hbig c hx b a]
  ring

/-- Invalid core assignments vanish on both sides, so the identity is valid
under the complete core assignment sum without a hidden admissibility premise. -/
theorem componentModeTerm_retained_all (x : CoreAt hN c→State)
    (b : ModeFiber hr hN hbig c→Bool) :
    componentModeTerm hr hd hN hbig c x b=componentCoreTerm hN radius c x*
      ∏ a : ModeFiber hr hN hbig c,retainedSourceMode N d hN a.val (choiceMode (b a))
        (localPortState hr hd hN hbig c x (firstModePort hr hN hbig c a))
        (localPortState hr hd hN hbig c x (lastModePort hr hN hbig c a)) := by
  by_cases hx : componentCoreAllowed hN c x
  · exact componentModeTerm_retained hr hd hN hbig c hx b
  · simp only [componentModeTerm,componentCoreTerm,if_neg hx,zero_mul]

end Geometry
end SubmittedGenus.CapFourMass.SourceCoreFactorization
