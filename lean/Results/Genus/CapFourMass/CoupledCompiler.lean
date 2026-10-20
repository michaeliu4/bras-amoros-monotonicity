import Results.Genus.CapFourMass.SourceExact
import Results.Genus.CapFourMass.CycleRunLayout
import Results.Genus.CapFourMass.RunAlternation
import Results.Genus.CapFourMass.AlternatingRuns
import Results.Genus.CapFourMass.RestrictedCounts

/-! Typed compilation of actual maximal runs into positive spectral pairs. -/
noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.CapFourMass.ActualComponent
open RawGraph RawGraph.Topology

inductive AtomicRun
  | strong (run : StrongRun)
  | carry (length : ℕ) (positive : 1≤length)

def AtomicRun.isStrong : AtomicRun→Bool
  | .strong _ => true
  | .carry _ _ => false

def AtomicRun.matrix : AtomicRun→Matrix State State ℝ
  | .strong s => s.matrix
  | .carry n _ => carryMatrix^n

def pairAtoms (b : CoupledRun) : List AtomicRun :=
  [.strong b.strong,.carry b.carryLength b.carryPositive]

lemma map_nonempty {A B : Type*} (f : A→B) (l : List A) (h : l≠[]) : l.map f≠[] :=
  fun he => h (List.map_eq_nil_iff.mp he)

/-- Every alternating strong-first/carry-last list has an actual typed
pairing; all carry exponents retain their positive-length proofs. -/
theorem pair_alternating_atoms (l : List AtomicRun) :
    l.IsChain (fun a b => a.isStrong≠b.isStrong) →
    (l.map AtomicRun.isStrong).head?=some true →
    (l.map AtomicRun.isStrong).getLast?=some false →
    ∃ bs : List CoupledRun,bs≠[] ∧ l=bs.flatMap pairAtoms := by
  induction l using List.twoStepInduction with
  | nil => intro _ hf _; simp at hf
  | singleton a =>
    intro _ hf hl
    cases a <;> simp [AtomicRun.isStrong] at hf hl
  | cons_cons a b l ih _ =>
    intro hchain hfirst hlast
    cases a with
    | carry n hn => simp [AtomicRun.isStrong] at hfirst
    | strong s =>
      cases b with
      | strong t =>
        have hh := hchain.rel
        exact (hh rfl).elim
      | carry n hn =>
        let block : CoupledRun := ⟨s,n,hn⟩
        by_cases hl : l=[]
        · subst l
          exact ⟨[block],by simp,by rfl⟩
        · have htail := hchain.tail.tail
          have hfst : (l.map AtomicRun.isStrong).head?=some true := by
            cases l with
            | nil => contradiction
            | cons a l =>
              have hh := hchain.tail.rel
              cases a <;> simp_all [AtomicRun.isStrong]
          have hlast' : (l.map AtomicRun.isStrong).getLast?=some false := by
            simpa only [List.map_cons,List.getLast?_cons_cons,
              List.getLast?_cons_of_ne_nil (map_nonempty _ _ hl)] using hlast
          obtain ⟨bs,hbs,he⟩ := ih htail hfst hlast'
          exact ⟨block::bs,by simp,by simp [pairAtoms,block,he]⟩

def compileRun (g : List EdgeKind) : AtomicRun :=
  if h : g=[] then .carry 1 (by omega) else
    match g.head h with
    | .strong => .strong (.full g.length (List.length_pos_iff.mpr h))
    | .restricted => .strong .restricted
    | .carry => .carry g.length (List.length_pos_iff.mpr h)

def sourceAtoms (l : List EdgeKind) : List AtomicRun :=
  (RunSegmentation.runs id l).map compileRun

lemma compileRun_color (g : List EdgeKind) (hg : g≠[]) :
    (compileRun g).isStrong=strongColor (g.head hg) := by
  unfold compileRun
  rw [dif_neg hg]
  cases g.head hg <;> rfl

lemma compileRun_matrix (l : List EdgeKind) (hl : l.IsChain CompatibleKinds)
    {g : List EdgeKind} (hg : g∈RunSegmentation.runs id l) :
    (compileRun g).matrix=(g.map EdgeKind.matrix).prod := by
  have hnon := RunSegmentation.run_nonempty id l hg
  rw [actual_run_power l hg]
  unfold compileRun
  rw [dif_neg hnon]
  split
  · simp_all [AtomicRun.matrix,StrongRun.matrix,EdgeKind.matrix]
  · have he : g=[.restricted] := restricted_run_singleton l hl hg (by assumption)
    subst g
    simp only [List.length_singleton,pow_one]
    rfl
  · simp_all [AtomicRun.matrix,EdgeKind.matrix]

lemma sourceAtoms_matrix (l : List EdgeKind) (hl : l.IsChain CompatibleKinds) :
    ((sourceAtoms l).map AtomicRun.matrix).prod=(l.map EdgeKind.matrix).prod := by
  rw [RunSegmentation.product_runs id l]
  unfold sourceAtoms
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro g hg
  exact compileRun_matrix l hl hg

lemma sourceAtoms_alternate (l : List EdgeKind) (hl : l.IsChain CompatibleKinds) :
    (sourceAtoms l).IsChain (fun a b => a.isStrong≠b.isStrong) := by
  unfold sourceAtoms
  rw [List.isChain_map]
  apply (run_heads_alternate_color l hl).imp_of_mem_imp
  intro g h hg hh hne
  obtain ⟨hgn,hhn,hne⟩ := hne
  simpa only [compileRun_color g hgn,compileRun_color h hhn] using hne

lemma pairAtoms_matrix (b : CoupledRun) : ((pairAtoms b).map AtomicRun.matrix).prod=b.matrix := by
  simp only [pairAtoms,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]
  rfl

lemma paired_matrix (bs : List CoupledRun) :
    ((bs.flatMap pairAtoms).map AtomicRun.matrix).prod=(bs.map CoupledRun.matrix).prod := by
  simp only [List.flatMap_def,List.map_flatten,List.prod_flatten,List.map_map,Function.comp_def,
    pairAtoms_matrix]

lemma sourceAtoms_head_color (l : List EdgeKind) :
    ((sourceAtoms l).map AtomicRun.isStrong).head?=(l.map strongColor).head? := by
  by_cases hl : l=[]
  · subst l; rfl
  have hr : RunSegmentation.runs id l≠[] := List.splitBy_ne_nil.mpr hl
  have hg := List.head_mem hr
  have hn := RunSegmentation.run_nonempty id l hg
  have hs : ((sourceAtoms l).map AtomicRun.isStrong)≠[] := by
    exact map_nonempty _ _ (map_nonempty _ _ hr)
  rw [List.head?_eq_some_head hs,List.head?_eq_some_head (map_nonempty _ _ hl)]
  simp only [sourceAtoms,List.head_map]
  rw [compileRun_color _ hn]
  exact congrArg some (congrArg strongColor (List.head_head_splitBy (fun a b : EdgeKind => decide (a=b)) hl))

lemma sourceAtoms_last_color (l : List EdgeKind) :
    ((sourceAtoms l).map AtomicRun.isStrong).getLast?=(l.map strongColor).getLast? := by
  by_cases hl : l=[]
  · subst l; rfl
  have hr : RunSegmentation.runs id l≠[] := List.splitBy_ne_nil.mpr hl
  have hg := List.getLast_mem hr
  have hn := RunSegmentation.run_nonempty id l hg
  have hs : ((sourceAtoms l).map AtomicRun.isStrong)≠[] := by
    exact map_nonempty _ _ (map_nonempty _ _ hr)
  rw [List.getLast?_eq_some_getLast hs,List.getLast?_eq_some_getLast (map_nonempty _ _ hl)]
  simp only [sourceAtoms,List.getLast_map]
  rw [compileRun_color _ hn]
  have he := RunSegmentation.run_constant id l hg
    ((RunSegmentation.runs id l).getLast hr |>.getLast hn) (List.getLast_mem hn)
  change ((RunSegmentation.runs id l).getLast hr).getLast hn=
    ((RunSegmentation.runs id l).getLast hr).head hn at he
  rw [← he]
  exact congrArg some (congrArg strongColor (List.getLast_getLast_splitBy (fun a b : EdgeKind => decide (a=b)) hl))

/-- The actual finite source cycle is compiled into a nonempty list of
positive-carry coupled blocks; no layout or source equality is assumed. -/
theorem actual_cycle_coupled {m r p : ℕ} (hp : RawGraph.Parameters m r p 4)
    (c : Component m r p) (hc : (freeComponentOrder m r p c).cycle=true) :
    ∃ (n : ℕ) (bs : List CoupledRun),bs≠[] ∧
      sourceAtoms ((closedWord c).rotate n)=bs.flatMap pairAtoms ∧
      componentMass c=((bs.map CoupledRun.matrix).prod).trace := by
  obtain ⟨n,hfirst,hlast,hchain,_,_⟩ := actual_cycle_run_cut hp c hc
  have hfirst' : ((sourceAtoms ((closedWord c).rotate n)).map AtomicRun.isStrong).head?=some true := by
    rw [sourceAtoms_head_color]; exact hfirst
  have hlast' : ((sourceAtoms ((closedWord c).rotate n)).map AtomicRun.isStrong).getLast?=some false := by
    rw [sourceAtoms_last_color]; exact hlast
  obtain ⟨bs,hbs,he⟩ := pair_alternating_atoms (sourceAtoms ((closedWord c).rotate n))
    (sourceAtoms_alternate _ hchain) hfirst' hlast'
  refine ⟨n,bs,hbs,he,?_⟩
  rw [componentMass_cycle_eq_word hp c hc,← matrix_word_trace_rotate EdgeKind.matrix (closedWord c) n,
    ← sourceAtoms_matrix _ hchain,he,paired_matrix]

end SubmittedGenus.CapFourMass.ActualComponent
