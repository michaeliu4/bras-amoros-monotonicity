import Results.Genus.GoldenGraph.Junctions

/-! Exact edge/run/junction identities for the original maximal source runs. -/
namespace SubmittedGenus.GoldenGraph
open RawGraph CapFourMass CapFourMass.ActualComponent
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

def strongPair (a b : EdgeKind) : ℕ := if a≠.carry ∧ b≠.carry then 1 else 0

def wordJunctions : List EdgeKind→ℕ
  | [] => 0
  | [_] => 0
  | a::b::l => strongPair a b+wordJunctions (b::l)

def boundaryJunction (l s : List EdgeKind) : ℕ :=
  strongPair (l.getLastD .carry) (s.headD .carry)

@[simp] lemma strongPair_carry_left (k : EdgeKind) : strongPair .carry k=0 := by simp [strongPair]
@[simp] lemma strongPair_carry_right (k : EdgeKind) : strongPair k .carry=0 := by simp [strongPair]

lemma wordJunctions_append (l s : List EdgeKind) :
    wordJunctions (l++s)=wordJunctions l+wordJunctions s+boundaryJunction l s := by
  induction l with
  | nil => simp [wordJunctions,boundaryJunction]
  | cons a l ih =>
    cases l with
    | nil => cases s <;> simp [wordJunctions,boundaryJunction,Nat.add_comm]
    | cons b l =>
      simp only [List.cons_append,wordJunctions] at ih ⊢
      rw [ih]
      have hb : boundaryJunction (a::b::l) s=boundaryJunction (b::l) s := by
        simp [boundaryJunction]
      rw [hb]
      omega

lemma wordJunctions_replicate (k : EdgeKind) (n : ℕ) :
    wordJunctions (List.replicate n k)=(n-1)*strongPair k k := by
  induction n with
  | zero => simp [wordJunctions]
  | succ n ih =>
    cases n with
    | zero => simp [wordJunctions]
    | succ n =>
      simp only [List.replicate_succ,wordJunctions] at ih ⊢
      rw [ih]
      simp only [Nat.add_sub_cancel,Nat.succ_mul]
      omega

lemma run_edge_junction_identity (l : List EdgeKind) {g : List EdgeKind}
    (hg : g∈RunSegmentation.runs id l) :
    strongLength g=(if g.headD .carry=.carry then 0 else 1)+wordJunctions g := by
  have hn:=RunSegmentation.run_nonempty id l hg
  let k:=g.head hn
  have he : g=List.replicate g.length k := List.eq_replicate_length.mpr
    (fun a ha => RunSegmentation.run_constant id l hg a ha)
  have hlen : 0<g.length := List.length_pos_iff.mpr hn
  have hhead : g.headD .carry=k := by
    cases g with
    | nil => contradiction
    | cons a gs => rfl
  rw [hhead,he,wordJunctions_replicate]
  simp only [strongLength,List.map_replicate,List.sum_replicate]
  by_cases hk : k=.carry
  · simp [hk,strongPair]
  · simp [hk,strongPair]
    omega

/-- Touching maximal strong/carry runs contribute no strong junction across
their boundary. This uses actual source compatibility, including isolated E runs. -/
lemma source_runs_boundary_zero (l : List EdgeKind) (hl : l.IsChain CompatibleKinds) :
    (RunSegmentation.runs id l).IsChain (fun g h => boundaryJunction g h=0) := by
  apply (run_heads_alternate_color l hl).imp_of_mem_imp
  intro g h hg hh hne
  obtain ⟨hgn,hhn,hne⟩:=hne
  have hg0:=RunSegmentation.run_constant id l hg (g.getLast hgn) (List.getLast_mem hgn)
  change g.getLast hgn=g.head hgn at hg0
  have hgD : g.getLastD .carry=g.getLast hgn := by simp only [List.getLastD_eq_getLast?,List.getLast?_eq_some_getLast hgn,Option.getD_some]
  have hhD : h.headD .carry=h.head hhn := by cases h with
    | nil => contradiction
    | cons a hs => rfl
  unfold boundaryJunction
  rw [hgD,hhD,hg0]
  by_cases ha : g.head hgn=.carry
  · simp [strongPair,ha]
  · by_cases hb : h.head hhn=.carry
    · simp [strongPair,hb]
    · exfalso
      apply hne
      exact (decide_eq_true_eq.mpr ha).trans (decide_eq_true_eq.mpr hb).symm

lemma wordJunctions_flatten (gs : List (List EdgeKind)) (hn : ∀ g∈gs,g≠[])
    (hb : gs.IsChain (fun g h => boundaryJunction g h=0)) :
    wordJunctions gs.flatten=(gs.map wordJunctions).sum := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    have hn' : ∀ h∈gs,h≠[] := fun h hh => hn h (List.mem_cons_of_mem g hh)
    rw [List.flatten_cons,wordJunctions_append,ih hn' hb.tail]
    have hz : boundaryJunction g gs.flatten=0 := by
      cases gs with
      | nil => simp [boundaryJunction]
      | cons h hs =>
        have hne:=hn' h (by simp)
        have hrel:=hb.rel
        change boundaryJunction g h=0 at hrel
        cases h with
        | nil => contradiction
        | cons a l => simpa only [boundaryJunction,List.flatten_cons,List.cons_append,List.headD_cons] using hrel
    simp only [hz,List.map_cons,List.sum_cons,Nat.add_zero]

def strongRunCount (l : List EdgeKind) : ℕ :=
  ((RunSegmentation.runs id l).map (fun g => if g.headD .carry=.carry then 0 else 1)).sum

/-- Exact maximal-source-run identity, before any analytic estimates. -/
theorem strong_runs_junction_identity (l : List EdgeKind) (hl : l.IsChain CompatibleKinds) :
    strongLength l=strongRunCount l+wordJunctions l := by
  have hm : ((RunSegmentation.runs id l).map strongLength)=
      (RunSegmentation.runs id l).map (fun g => (if g.headD .carry=.carry then 0 else 1)+wordJunctions g) :=
    List.map_congr_left (fun g hg => run_edge_junction_identity l hg)
  rw [(run_exponents_preserved l).1,hm,List.sum_map_add]
  have hj:=wordJunctions_flatten (RunSegmentation.runs id l)
    (fun g hg => RunSegmentation.run_nonempty id l hg) (source_runs_boundary_zero l hl)
  rw [RunSegmentation.flatten_runs] at hj
  exact congrArg (fun n => strongRunCount l+n) hj.symm

lemma wordJunctions_ofFn (n : ℕ) (f : Fin (n+1)→EdgeKind) :
    wordJunctions (List.ofFn f)=∑ j : Fin n,strongPair (f j.castSucc) (f j.succ) := by
  induction n with
  | zero => simp [List.ofFn_succ,wordJunctions]
  | succ n ih =>
    rw [List.ofFn_succ,List.ofFn_succ]
    rw [wordJunctions,← List.ofFn_succ (f:=fun j : Fin (n+1) => f j.succ),ih,Fin.sum_univ_succ]
    rfl

abbrev WordJunction (n : ℕ) (f : Fin n→EdgeKind) :=
  {j : Fin (n-1) //
    f ⟨j.val,by have:=j.isLt; omega⟩≠.carry ∧
    f ⟨j.val+1,by have:=j.isLt; omega⟩≠.carry}

lemma wordJunctions_card (n : ℕ) (f : Fin n→EdgeKind) :
    wordJunctions (List.ofFn f)=Fintype.card (WordJunction n f) := by
  cases n with
  | zero => simp [wordJunctions,WordJunction]
  | succ n =>
    rw [wordJunctions_ofFn,Fintype.card_subtype,Finset.card_filter]
    apply Finset.sum_congr rfl
    intro j _
    rfl

def cyclicWordJunctions (l : List EdgeKind) : ℕ := wordJunctions l+boundaryJunction l l

lemma cyclicWordJunctions_rotate_one (l : List EdgeKind) :
    cyclicWordJunctions (l.rotate 1)=cyclicWordJunctions l := by
  cases l with
  | nil => simp
  | cons a l =>
    cases l with
    | nil => simp
    | cons b l =>
      rw [show 1=0+1 from rfl,List.rotate_cons_succ,List.rotate_zero]
      have hb : boundaryJunction ((b::l)++[a]) ((b::l)++[a])=strongPair a b := by
        unfold boundaryJunction
        rw [List.getLastD_concat]
        rfl
      unfold cyclicWordJunctions
      rw [wordJunctions_append,hb]
      simp [wordJunctions,boundaryJunction,Nat.add_comm,Nat.add_left_comm]

lemma cyclicWordJunctions_rotate (l : List EdgeKind) (n : ℕ) :
    cyclicWordJunctions (l.rotate n)=cyclicWordJunctions l := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← List.rotate_rotate,cyclicWordJunctions_rotate_one,ih]

end
end SubmittedGenus.GoldenGraph
