import Results.Genus.FixedPivot.Progression
import Results.Genus.FixedPivot.TailLayout

/-! Exact phase counts from the original carry-component layout, retaining loops. -/
namespace SubmittedGenus.FixedPivot
open scoped BigOperators

section PhaseCounts
variable (N d : ℕ) (hd : 0<d) (hN : d<N)

abbrev CarryFixedRepresentative :=
  {a : CarryRepresentative N d hN // a.val=portPartner N d hN a.val}

/-- Actual fixed port classes, rather than a supplied scalar count. -/
def carryFixedCount : ℕ := Fintype.card (CarryFixedRepresentative N d hN)

abbrev CarryLoop :=
  {x : Fin N // 0<x.val ∧ CarryIncidence N d x.val x.val}

def carryFixedTerminal (a : CarryFixedRepresentative N d hN) : CarryLoop N d :=
  ⟨⟨carryComponentLabel N d hN a.val (carryComponentSize N d hN a.val-1),
    (carryComponentLabel_vertex N d hN a.val (by
      have := carryComponentSize_positive N d hN a.val; omega)).2⟩,
    (carryComponentLabel_vertex N d hN a.val (by
      have := carryComponentSize_positive N d hN a.val; omega)).1,
    (carry_component_incidence_iff N d hN a.val (by
      have := carryComponentSize_positive N d hN a.val; omega) (by
      have := carryComponentSize_positive N d hN a.val; omega)).2
        (Or.inr (Or.inr ⟨a.property,rfl,rfl⟩))⟩

include hd in
lemma carryFixedTerminal_injective : Function.Injective (carryFixedTerminal N d hN) := by
  intro a b he
  apply Subtype.ext
  apply carryComponentLabel_disjoint N d hd hN
    a.val b.val (carryComponentSize N d hN a.val-1) (carryComponentSize N d hN b.val-1)
  exact congrArg (fun x : CarryLoop N d => x.val.val) he

include hd in
lemma carryFixedTerminal_surjective : Function.Surjective (carryFixedTerminal N d hN) := by
  intro x
  obtain ⟨a,t,ht⟩ := carryComponentLabel_surjective N d hd hN ⟨x.property.1,x.val.isLt⟩
  have hi : CarryIncidence N d (carryComponentLabel N d hN a t.val)
      (carryComponentLabel N d hN a t.val) := by rw [ht]; exact x.property.2
  obtain h | h | ⟨hf,hterm,_⟩ := (carry_component_incidence_iff N d hN a t.isLt t.isLt).1 hi
  · omega
  · omega
  · refine ⟨⟨a,hf⟩,?_⟩
    apply Subtype.ext
    apply Fin.ext
    change carryComponentLabel N d hN a (carryComponentSize N d hN a-1)=x.val.val
    rwa [← hterm]

/-- Fixed port classes are exactly the actual self-incidences at the path terminals. -/
noncomputable def carryFixedLoopEquiv : CarryFixedRepresentative N d hN ≃ CarryLoop N d :=
  Equiv.ofBijective (carryFixedTerminal N d hN)
    ⟨carryFixedTerminal_injective N d hd hN,carryFixedTerminal_surjective N d hd hN⟩

abbrev CarryLoopPhase := {b : Bool // (if b then N+d else N)%2=0}

def carryLoopFromPhase (b : CarryLoopPhase N d) : CarryLoop N d := by
  let S := if b.val then N+d else N
  have hS : S%2=0 := b.property
  have hlow : 0<S/2 := by dsimp [S]; split_ifs <;> omega
  have hupp : S/2<N := by dsimp [S]; split_ifs <;> omega
  refine ⟨⟨S/2,hupp⟩,hlow,?_⟩
  unfold CarryIncidence
  cases hb : b.val
  · left
    simp only [S,hb,Bool.false_eq_true,↓reduceIte] at hS ⊢
    omega
  · right
    simp only [S,hb,↓reduceIte] at hS ⊢
    omega

lemma carryLoopFromPhase_injective : Function.Injective (carryLoopFromPhase N d hd hN) := by
  intro a b he
  have hv := congrArg (fun x : CarryLoop N d => x.val.val) he
  have ha := a.property
  have hb := b.property
  apply Subtype.ext
  cases hat : a.val <;> cases hbt : b.val <;> try rfl
  all_goals simp only [carryLoopFromPhase,hat,hbt,Bool.false_eq_true,↓reduceIte] at hv ha hb
  all_goals omega

lemma carryLoopFromPhase_surjective : Function.Surjective (carryLoopFromPhase N d hd hN) := by
  intro x
  rcases x.property.2 with h | h
  · have hp : N%2=0 := by omega
    refine ⟨⟨false,hp⟩,?_⟩
    apply Subtype.ext
    apply Fin.ext
    change N/2=x.val.val
    omega
  · have hp : (N+d)%2=0 := by omega
    refine ⟨⟨true,hp⟩,?_⟩
    apply Subtype.ext
    apply Fin.ext
    change (N+d)/2=x.val.val
    omega

/-- The two possible source reflections contribute one loop exactly when their sum is even. -/
noncomputable def carryLoopPhaseEquiv : CarryLoopPhase N d ≃ CarryLoop N d :=
  Equiv.ofBijective (carryLoopFromPhase N d hd hN)
    ⟨carryLoopFromPhase_injective N d hd hN,carryLoopFromPhase_surjective N d hd hN⟩

include hd in
theorem carryFixedCount_eq_loop_phases :
    carryFixedCount N d hN = (if N%2=0 then 1 else 0)+(if (N+d)%2=0 then 1 else 0) := by
  unfold carryFixedCount
  rw [Fintype.card_congr ((carryFixedLoopEquiv N d hd hN).trans
    (carryLoopPhaseEquiv N d hd hN).symm)]
  rw [Fintype.card_subtype]
  rw [Fintype.univ_bool]
  by_cases h0 : N%2=0 <;> by_cases h1 : (N+d)%2=0 <;> simp [Finset.filter_insert,Finset.filter_singleton,h0,h1]

include hd in
theorem carryFixedCount_odd (ho : Odd d) : carryFixedCount N d hN=1 := by
  rw [carryFixedCount_eq_loop_phases N d hd hN]
  have hp := Nat.odd_iff.mp ho
  split_ifs <;> omega

include hd in
theorem carryFixedCount_even_odd (he : Even d) (ho : Odd N) :
    carryFixedCount N d hN=0 := by
  rw [carryFixedCount_eq_loop_phases N d hd hN]
  have hpd := Nat.even_iff.mp he
  have hpN := Nat.odd_iff.mp ho
  split_ifs <;> omega

include hd in
theorem carryFixedCount_even_even (he : Even d) (hNe : Even N) :
    carryFixedCount N d hN=2 := by
  rw [carryFixedCount_eq_loop_phases N d hd hN]
  have hpd := Nat.even_iff.mp he
  have hpN := Nat.even_iff.mp hNe
  split_ifs <;> omega

/-- The actual carry-vertex interval has exactly N−1 positions. -/
def carryVertexIndexEquiv : {x : ℕ // CarryVertex N x} ≃ Fin (N-1) where
  toFun x := ⟨x.val-1,by have := x.property; unfold CarryVertex at this; omega⟩
  invFun i := ⟨i.val+1,by have := i.isLt; unfold CarryVertex; omega⟩
  left_inv x := by apply Subtype.ext; have := x.property.1; dsimp; omega
  right_inv i := by apply Fin.ext; simp

include hd in
/-- Exhaustive source layout gives the total vertex count without a counting assumption. -/
theorem carryComponent_total_vertices :
    (∑ a : CarryRepresentative N d hN, carryComponentSize N d hN a)=N-1 := by
  have hc := Fintype.card_congr ((carryLayoutEquiv N d hd hN).trans (carryVertexIndexEquiv N d))
  simpa only [Fintype.card_sigma,Fintype.card_fin] using hc

/-- Orbit counting is derived from the proved port-slot bijection. -/
theorem carryRepresentative_card_twice :
    2*Fintype.card (CarryRepresentative N d hN)=d+carryFixedCount N d hN := by
  have hs : (∑ a : CarryRepresentative N d hN,
      (carryPortArity N d hN a + if a.val=portPartner N d hN a.val then 1 else 0))=
      2*Fintype.card (CarryRepresentative N d hN) := by
    have he : ∀ a : CarryRepresentative N d hN,
        carryPortArity N d hN a+(if a.val=portPartner N d hN a.val then 1 else 0)=2 := by
      intro a
      unfold carryPortArity
      split_ifs <;> rfl
    simp_rw [he]
    simp [Nat.mul_comm]
  rw [Finset.sum_add_distrib,carry_port_arity_sum] at hs
  have hf : (∑ a : CarryRepresentative N d hN,
      if a.val=portPartner N d hN a.val then 1 else 0)=carryFixedCount N d hN := by
    simp [carryFixedCount,Fintype.card_subtype]
  rw [hf] at hs
  exact hs.symm

/-- Number of ordinary edges in the exact canonical carry paths before pivot deletion. -/
def carryFullPathEdgeCount : ℕ :=
  ∑ a : CarryRepresentative N d hN, (carryComponentSize N d hN a-1)

include hd in
theorem carryFullPathEdgeCount_add_components :
    carryFullPathEdgeCount N d hN+Fintype.card (CarryRepresentative N d hN)=N-1 := by
  have hh : (∑ a : CarryRepresentative N d hN,
      ((carryComponentSize N d hN a-1)+1))=
      ∑ a : CarryRepresentative N d hN,carryComponentSize N d hN a := by
    apply Finset.sum_congr rfl
    intro a _
    have hp := carryComponentSize_positive N d hN a
    omega
  rw [Finset.sum_add_distrib] at hh
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one] at hh
  rw [carryComponent_total_vertices N d hd hN] at hh
  exact hh

include hd in
/-- Exact source floor formula, including both reflection phases. -/
theorem carryFullPathEdgeCount_eq :
    carryFullPathEdgeCount N d hN=(N-1)/2+(N-d-1)/2 := by
  have hv := carryFullPathEdgeCount_add_components N d hd hN
  have hc := carryRepresentative_card_twice N d hN
  have hf := carryFixedCount_eq_loop_phases N d hd hN
  split_ifs at hf <;> omega

/-- Actual unordered ordinary carry edges after deleting pivot d, represented
by their uniquely increasing endpoint pair. -/
def carrySourceEdgeSet : Finset (ℕ×ℕ) :=
  ((Finset.Icc 1 ((N-1)/2)).erase d).image (fun x => (x,N-x)) ∪
    (Finset.Icc (d+1) ((N+d-1)/2)).image (fun x => (x,N+d-x))

def carrySourceEdgeCount : ℕ := (carrySourceEdgeSet N d).card

include hd in
/-- Membership is exactly the source carry relation on surviving, distinct vertices. -/
theorem carrySourceEdgeSet_mem_iff (hbig : 2*d<N) (x y : ℕ) :
    (x,y)∈carrySourceEdgeSet N d ↔
      0<x ∧ x<y ∧ y<N ∧ x≠d ∧ y≠d ∧ CarryIncidence N d x y := by
  simp only [carrySourceEdgeSet,Finset.mem_union,Finset.mem_image,Finset.mem_erase,
    Finset.mem_Icc,Prod.mk.injEq]
  constructor
  · rintro (⟨a,⟨hne,ha1,ha2⟩,hax,hay⟩ | ⟨a,⟨ha1,ha2⟩,hax,hay⟩)
    · unfold CarryIncidence
      omega
    · unfold CarryIncidence
      omega
  · rintro ⟨hx,hxy,hy,hxd,hyd,hinc⟩
    rcases hinc with h | h
    · left
      exact ⟨x,⟨hxd,by omega,by omega⟩,rfl,by omega⟩
    · right
      exact ⟨x,⟨by omega,by omega⟩,rfl,by omega⟩

include hd in
theorem carrySourceEdgeCount_eq (hbig : 2*d<N) :
    carrySourceEdgeCount N d=(N-1)/2+(N-d-1)/2-1 := by
  have hdis : Disjoint
      (((Finset.Icc 1 ((N-1)/2)).erase d).image (fun x => (x,N-x)))
      ((Finset.Icc (d+1) ((N+d-1)/2)).image (fun x => (x,N+d-x))) := by
    apply Finset.disjoint_left.mpr
    intro xy hf hg
    obtain ⟨a,ha,he⟩ := Finset.mem_image.mp hf
    obtain ⟨b,hb,he'⟩ := Finset.mem_image.mp hg
    have hab := congrArg Prod.fst (he.trans he'.symm)
    have ht := congrArg Prod.snd (he.trans he'.symm)
    have hb' := Finset.mem_Icc.mp hb
    dsimp at hab ht
    omega
  have hinjF : Function.Injective (fun x : ℕ => (x,N-x)) := by
    intro x y h
    exact congrArg Prod.fst h
  have hinjG : Function.Injective (fun x : ℕ => (x,N+d-x)) := by
    intro x y h
    exact congrArg Prod.fst h
  have hp : d∈Finset.Icc 1 ((N-1)/2) := Finset.mem_Icc.mpr ⟨by omega,by omega⟩
  unfold carrySourceEdgeCount carrySourceEdgeSet
  rw [Finset.card_union_of_disjoint hdis,Finset.card_image_of_injective _ hinjF,
    Finset.card_image_of_injective _ hinjG,Finset.card_erase_of_mem hp]
  simp only [Nat.card_Icc]
  omega

include hd in
/-- Deleting the actual pivot removes exactly one ordinary edge from the full layout. -/
theorem carrySourceEdgeCount_eq_full_sub_one (hbig : 2*d<N) :
    carrySourceEdgeCount N d=carryFullPathEdgeCount N d hN-1 := by
  rw [carrySourceEdgeCount_eq N d hd hbig,carryFullPathEdgeCount_eq N d hd hN]

include hd in
/-- Across adjacent multiplicities with odd d, the full source edge count grows by one. -/
theorem carrySourceEdgeCount_odd_step (hbig : 2*d<N) (ho : Odd d) :
    carrySourceEdgeCount (N+1) d=carrySourceEdgeCount N d+1 := by
  rw [carrySourceEdgeCount_eq (N+1) d hd (by omega),carrySourceEdgeCount_eq N d hd hbig]
  have hp := Nat.odd_iff.mp ho
  omega

include hd in
/-- With even d, the parity-preserving source phase step grows by two edges. -/
theorem carrySourceEdgeCount_even_step (hbig : 2*d<N) (_he : Even d) :
    carrySourceEdgeCount (N+2) d=carrySourceEdgeCount N d+2 := by
  rw [carrySourceEdgeCount_eq (N+2) d hd (by omega),carrySourceEdgeCount_eq N d hd hbig]
  omega

/-- Equivalent finite-set form of the actual fixed-class count. -/
theorem carryFixedCount_eq_filter :
    carryFixedCount N d hN =
      (Finset.univ.filter (fun a : CarryRepresentative N d hN =>
        a.val=portPartner N d hN a.val)).card := by
  exact Fintype.card_subtype _

include hd in
theorem carryFixedCount_odd_step (ho : Odd d) :
    carryFixedCount (N+1) d (by omega)=carryFixedCount N d hN := by
  rw [carryFixedCount_odd (N+1) d hd (by omega) ho,carryFixedCount_odd N d hd hN ho]

include hd in
theorem carryFixedCount_parity_step :
    carryFixedCount (N+2) d (by omega)=carryFixedCount N d hN := by
  rw [carryFixedCount_eq_loop_phases (N+2) d hd (by omega),
    carryFixedCount_eq_loop_phases N d hd hN]
  have h0 : (N+2)%2=N%2 := by omega
  have h1 : (N+2+d)%2=(N+d)%2 := by omega
  rw [h0,h1]

/-- The fixed loop classes survive the pivot deletion in every source phase. -/
theorem carryLoop_ne_pivot (hbig : 2*d<N) (x : CarryLoop N d) : x.val.val≠d := by
  have hh := x.property.2
  unfold CarryIncidence at hh
  omega

include hd in
/-- The two actual counts needed for the all-multiplicity odd-d cancellation step. -/
theorem carryCounts_odd_step (hbig : 2*d<N) (ho : Odd d) :
    carryFixedCount (N+1) d (by omega)=carryFixedCount N d hN ∧
      carrySourceEdgeCount (N+1) d=carrySourceEdgeCount N d+1 :=
  ⟨carryFixedCount_odd_step N d hd hN ho,carrySourceEdgeCount_odd_step N d hd hbig ho⟩

include hd in
/-- The two actual counts on either parity progression when d is even. -/
theorem carryCounts_even_step (hbig : 2*d<N) (he : Even d) :
    carryFixedCount (N+2) d (by omega)=carryFixedCount N d hN ∧
      carrySourceEdgeCount (N+2) d=carrySourceEdgeCount N d+2 :=
  ⟨carryFixedCount_parity_step N d hd hN,carrySourceEdgeCount_even_step N d hd hbig he⟩

/-- Each actual carry-tail position contributes one fewer ordinary internal edge. -/
def carryTailPathEdgeCount : ℕ :=
  ∑ a : CarryRepresentative N d hN, (carryTailSize N d hN a-1)

include hd in
theorem carryTail_total_vertices (hbig : 2*d<N) :
    (∑ a : CarryRepresentative N d hN,carryTailSize N d hN a)+d=N-1 := by
  have hh : (∑ a : CarryRepresentative N d hN,
      (carryTailSize N d hN a+carryPortArity N d hN a))=
      ∑ a : CarryRepresentative N d hN,carryComponentSize N d hN a := by
    apply Finset.sum_congr rfl
    intro a _
    have hp := carryTailSize_positive N d hN hbig a
    unfold carryTailSize at hp ⊢
    omega
  rw [Finset.sum_add_distrib,carry_port_arity_sum,
    carryComponent_total_vertices N d hd hN] at hh
  exact hh

include hd in
/-- Exact internal tail edges plus the surviving d−1 core-to-tail attachments
recover all surviving source carry edges. -/
theorem carryTailPathEdgeCount_add_ports (hbig : 2*d<N) :
    carryTailPathEdgeCount N d hN+(d-1)=carrySourceEdgeCount N d := by
  have hh : (∑ a : CarryRepresentative N d hN,
      ((carryTailSize N d hN a-1)+1))=
      ∑ a : CarryRepresentative N d hN,carryTailSize N d hN a := by
    apply Finset.sum_congr rfl
    intro a _
    have hp := carryTailSize_positive N d hN hbig a
    omega
  rw [Finset.sum_add_distrib] at hh
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one] at hh
  change carryTailPathEdgeCount N d hN+Fintype.card (CarryRepresentative N d hN)=_ at hh
  have hv := carryTail_total_vertices N d hd hN hbig
  have he := carryFullPathEdgeCount_add_components N d hd hN
  rw [carrySourceEdgeCount_eq_full_sub_one N d hd hN hbig]
  omega


end PhaseCounts

/-- The finite edge set is exactly the original raw graph's free binary carry
relation, expressed in shifted coordinates and oriented by physical order. -/
theorem carrySourceEdgeSet_rawGraph_iff {m r p : ℕ} (hrp : r<p) (hmp : 2*p<m)
    (i j : Fin (m-1)) :
    (RawGraph.physical i-r,RawGraph.physical j-r)∈carrySourceEdgeSet (m-r) (p-r) ↔
      RawGraph.physical i<RawGraph.physical j ∧ RawGraph.IsFree r p i ∧
        RawGraph.IsFree r p j ∧
        (RawGraph.physical i+RawGraph.physical j=m+r ∨
          RawGraph.physical i+RawGraph.physical j=m+p) := by
  rw [carrySourceEdgeSet_mem_iff (m-r) (p-r) (by omega) (by omega)]
  have hi := i.isLt
  have hj := j.isLt
  unfold RawGraph.IsFree RawGraph.IsPivot RawGraph.physical CarryIncidence
  omega

end SubmittedGenus.FixedPivot
