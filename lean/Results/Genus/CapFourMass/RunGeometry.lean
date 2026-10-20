import Results.Genus.CapFourMass.RunLayout

/-! Actual adjacency forbids extending a restricted E edge by a strong edge. -/
noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.CapFourMass.ActualComponent
open RawGraph RawGraph.SourceModel RawGraph.Topology

lemma kind_symm {m r p : ℕ} (i j : Fin (m-1)) : kind r p i j=kind r p j i := by
  unfold kind
  simp only [Nat.add_comm,and_comm]

lemma vertex_injective {m r p : ℕ} (c : Component m r p) : Function.Injective (vertex c) :=
  StrongRuns.componentPhysicalVertex_injective c

def CompatibleKinds (a b : EdgeKind) : Prop :=
  (a=.restricted → b=.carry) ∧ (b=.restricted → a=.carry)

lemma neighbor_compatible {m r p : ℕ} (hp : Parameters m r p 4) {i j k : Fin (m-1)}
    (hij : (rawGraph m r p).Adj i j) (hjk : (rawGraph m r p).Adj j k) (hne : i≠k) :
    CompatibleKinds (kind r p i j) (kind r p j k) := by
  constructor
  · intro he
    exact (kind_carry_iff hp hjk).2 (restricted_neighbor_carry hij he hjk hne)
  · intro he
    have hr : kind r p k j=.restricted := (kind_symm _ _).symm.trans he
    have hh := restricted_neighbor_carry hjk.symm hr hij.symm hne.symm
    exact (kind_carry_iff hp hij).2 (StrongRuns.carryStep_symm hh)

lemma pathWord_compatible {m r p : ℕ} (hp : Parameters m r p 4) (c : Component m r p) :
    (pathWord c).IsChain CompatibleKinds := by
  rw [List.isChain_iff_getElem]
  intro j hj
  have hj' : j+1<edgeCount c := by simpa only [pathWord_length] using hj
  have hj0 : j<edgeCount c := by omega
  simp only [pathWord,List.getElem_ofFn]
  have he := neighbor_compatible hp (consecutive_adj c ⟨j,hj0⟩) (consecutive_adj c ⟨j+1,hj'⟩)
  have hne : vertex c (Fin.castSucc ⟨j,hj0⟩) ≠ vertex c (Fin.succ ⟨j+1,hj'⟩) := by
    intro h
    have hh := congrArg Fin.val (vertex_injective c h)
    simp only [Fin.val_castSucc,Fin.val_succ] at hh
    omega
  exact he hne

lemma closedWord_compatible {m r p : ℕ} (hp : Parameters m r p 4) (c : Component m r p)
    (hc : (freeComponentOrder m r p c).cycle=true) : (closedWord c).IsChain CompatibleKinds := by
  have hn : 3≤edgeCount c := (freeComponentOrder m r p c).cycle_min hc
  have hnon : pathWord c≠[] := by intro h; have := congrArg List.length h; simp at this; omega
  unfold closedWord
  apply List.IsChain.append (pathWord_compatible hp c) (by simp)
  intro a ha b hb
  rw [List.getLast?_eq_some_getLast hnon] at ha
  have ha' : a=(pathWord c).getLast hnon := (Option.mem_some_iff.mp ha).symm
  have hb' : b=kind r p (vertex c (Fin.last _)) (vertex c 0) := by simpa using (Option.mem_some_iff.mp hb).symm
  subst a; subst b
  simp only [pathWord,List.getLast_ofFn]
  have hlast : edgeCount c-1<edgeCount c := by omega
  have hcast : Fin.succ (⟨edgeCount c-1,hlast⟩ : Fin (edgeCount c))=Fin.last (edgeCount c) := by
    apply Fin.ext
    simp only [Fin.val_succ,Fin.val_last]
    omega
  have he := consecutive_adj c ⟨edgeCount c-1,hlast⟩
  rw [hcast] at he ⊢
  apply neighbor_compatible hp he (closing_adj c hc)
  intro h
  have hh := congrArg Fin.val (vertex_injective c h)
  simp only [Fin.val_castSucc,Fin.val_zero] at hh
  omega

/-- Every monochromatic restricted block compiled from an actual source word
has length exactly one; no unsupported E-power spectral estimate is needed. -/
lemma restricted_run_singleton (l : List EdgeKind) (hl : l.IsChain CompatibleKinds)
    {g : List EdgeKind} (hg : g∈RunSegmentation.runs id l)
    (he : g.head (RunSegmentation.run_nonempty id l hg)=.restricted) : g=[.restricted] := by
  have hinfix : List.IsInfix g l := by
    rw [← RunSegmentation.flatten_runs id l]
    exact List.infix_of_mem_flatten hg
  have hchain : g.IsChain CompatibleKinds := by
    obtain ⟨a,b,hab⟩ := hinfix
    subst l
    exact (hl.left_of_append).right_of_append
  cases g with
  | nil => exact (RunSegmentation.run_nonempty id l hg rfl).elim
  | cons a xs =>
    have ha : a=.restricted := he
    subst a
    cases xs with
    | nil => rfl
    | cons b bs =>
      have hb := RunSegmentation.run_constant id l hg b (by simp)
      change b=.restricted at hb
      have hc := hchain.rel
      have hh : b=.carry := hc.1 rfl
      exact (by cases hb.symm.trans hh)

end SubmittedGenus.CapFourMass.ActualComponent
