import Results.Genus.CapFourMass.RunGeometry

/-! Internal source alphabet masks are forced by the actual ordinary edges. -/
noncomputable section
namespace SubmittedGenus.CapFourMass.ActualComponent
open RawGraph RawGraph.SourceModel RawGraph.Topology

def BaseAllowed {m : ℕ} (r p : ℕ) (i j : Fin (m-1)) (v w : State) : Prop :=
  match kind r p i j with
  | .strong => gate 4 4 v w
  | .restricted => gate 4 3 v w
  | .carry => gate 3 3 v w

instance {m r p : ℕ} (i j : Fin (m-1)) (v w : State) : Decidable (BaseAllowed r p i j v w) := by
  unfold BaseAllowed
  split <;> infer_instance

lemma baseAllowed_symm {m r p : ℕ} (i j : Fin (m-1)) (v w : State) :
    BaseAllowed r p i j v w ↔ BaseAllowed r p j i w v := by
  unfold BaseAllowed
  rw [kind_symm i j]
  cases kind r p j i <;> simp [gate,and_comm,and_left_comm,and_assoc,Nat.add_comm]

lemma baseMatrix_eq_gate {m r p : ℕ} (i j : Fin (m-1)) (v w : State) :
    baseMatrix r p i j v w = if BaseAllowed r p i j v w then halfWeight v*halfWeight w else 0 := by
  unfold baseMatrix BaseAllowed kind
  split_ifs <;> simp_all [strongMatrix,restrictedMatrix,carryMatrix,transfer]

lemma baseAllowed_iff_of_domains {m r p : ℕ} (hp : Parameters m r p 4)
    (c : Component m r p) (i j : Fin (edgeCount c+1))
    (he : (rawGraph m r p).Adj (vertex c i) (vertex c j)) (v w : State)
    (hv : Domain r p 4 (vertex c i) (v.val+1)) (hw : Domain r p 4 (vertex c j) (w.val+1)) :
    BaseAllowed r p (vertex c i) (vertex c j) v w ↔
      edgeBound r p 4 (vertex c i) (vertex c j)≤(v.val+1)+(w.val+1) := by
  have vv:=v.isLt; have ww:=w.isLt
  unfold BaseAllowed kind
  rcases StrongRuns.edge_strong_or_carry he with hs | hc
  · rw [if_pos hs.2,strong_edgeBound hs]
    split_ifs with hh
    · have hv3:=domain_value_le_three c i hh.1 v hv
      have hw3:=domain_value_le_three c j hh.2 w hw
      simp only [gate]
      omega
    · simp only [gate]
      omega
  · have hn : ¬(physical (vertex c i)+physical (vertex c j)=r ∨
        physical (vertex c i)+physical (vertex c j)=p) := by
      intro hs
      exact StrongRuns.strong_carry_disjoint hp _ _ ⟨⟨he,hs⟩,hc⟩
    rw [if_neg hn,carry_edgeBound hp hc]
    have hv3:=StrongRuns.carry_domain_upper hp hc hv
    have hw3:=StrongRuns.carry_domain_upper hp (StrongRuns.carryStep_symm hc) hw
    simp only [gate]
    omega

lemma baseAllowed_bound {m r p : ℕ} (hp : Parameters m r p 4) {i j : Fin (m-1)}
    (he : (rawGraph m r p).Adj i j) (v w : State) (hb : BaseAllowed r p i j v w) :
    edgeBound r p 4 i j≤(v.val+1)+(w.val+1) := by
  rcases StrongRuns.edge_strong_or_carry he with hs | hc
  · rw [strong_edgeBound hs]
    unfold BaseAllowed kind at hb
    rw [if_pos hs.2] at hb
    split_ifs at hb <;> exact hb.2.2
  · rw [carry_edgeBound hp hc]
    unfold BaseAllowed at hb
    rw [(kind_carry_iff hp he).2 hc] at hb
    exact hb.2.2

lemma baseAllowed_carry_upper {m r p : ℕ} (hp : Parameters m r p 4) {i j : Fin (m-1)}
    (he : StrongRuns.CarryStep r p i j) (v w : State) (hb : BaseAllowed r p i j v w) : v.val+1≤3 := by
  unfold BaseAllowed at hb
  rw [(kind_carry_iff hp he.1).2 he] at hb
  exact hb.1

/-- At any internal source vertex, all unary constraints already follow from
its two incident D/E/C gates. Loops are impossible there. -/
theorem domain_of_two_base_gates {m r p : ℕ} (hp : Parameters m r p 4)
    {i j k : Fin (m-1)} (hj : (rawGraph m r p).Adj i j) (hk : (rawGraph m r p).Adj i k)
    (hne : j≠k) (v w u : State) (h1 : BaseAllowed r p i j v w) (h2 : BaseAllowed r p i k v u) :
    Domain r p 4 i (v.val+1) := by
  have hloop : ¬(StrongLoop r p i ∨ CarryLoop r p i) :=
    fun h => hne (StrongRuns.loop_excludes_two_neighbors h hj hk)
  have hv := v.isLt
  have hupper : v.val+1≤upper r 4 i := by
    by_cases hi : physical i<r
    · simp only [upper,if_pos hi]; omega
    · have hc : StrongRuns.CarryStep r p i j ∨ StrongRuns.CarryStep r p i k := by
        rcases StrongRuns.edge_strong_or_carry hj with hs | hc
        · rcases StrongRuns.edge_strong_or_carry hk with hs' | hc'
          · exact (hi (StrongRuns.internal_strong_lt_r hs hs' hne)).elim
          · exact Or.inr hc'
        · exact Or.inl hc
      have hv3 : v.val+1≤3 := by
        rcases hc with hc | hc
        · exact baseAllowed_carry_upper hp hc v w h1
        · exact baseAllowed_carry_upper hp hc v u h2
      simpa only [upper,if_neg hi] using hv3
  rw [domain_iff_unary]
  refine ⟨fun h => (hj.2.1 h).elim,fun _ => ⟨by omega,hupper,?_,?_⟩⟩
  · exact fun h => (hloop (Or.inl h)).elim
  · exact fun h => (hloop (Or.inr h)).elim

/-- Only true path endpoints need explicit unary masks in an unmasked edge word. -/
def BoundaryAllowed {m r p : ℕ} (c : Component m r p) (x : Fin (edgeCount c+1)→State) : Prop :=
  (freeComponentOrder m r p c).cycle=false →
    Domain r p 4 (vertex c 0) ((x 0).val+1) ∧
    Domain r p 4 (vertex c (Fin.last _)) ((x (Fin.last _)).val+1)

def AllBaseAllowed {m r p : ℕ} (c : Component m r p) (x : Fin (edgeCount c+1)→State) : Prop :=
  ∀ i j,(rawGraph m r p).Adj (vertex c i) (vertex c j) → BaseAllowed r p (vertex c i) (vertex c j) (x i) (x j)

lemma all_base_implies_domains {m r p : ℕ} (hp : Parameters m r p 4)
    (c : Component m r p) (x : Fin (edgeCount c+1)→State)
    (hb : BoundaryAllowed c x) (he : AllBaseAllowed c x) :
    ∀ i,Domain r p 4 (vertex c i) ((x i).val+1) := by
  intro i
  by_cases hc : (freeComponentOrder m r p c).cycle=true
  · obtain ⟨j,k,hj,hk,hne⟩ := StrongRuns.cycle_two_neighbors (freeComponentOrder m r p c) hc i
    exact domain_of_two_base_gates hp hj hk (fun h => hne (vertex_injective c h))
      (x i) (x j) (x k) (he i j hj) (he i k hk)
  · have hc' : (freeComponentOrder m r p c).cycle=false := Bool.eq_false_iff.mpr hc
    by_cases hi0 : i=0
    · subst i; exact (hb hc').1
    by_cases hin : i=Fin.last (edgeCount c)
    · subst i; exact (hb hc').2
    have hi := i.isLt
    have h0 : 0 < (i.val : ℕ) := by
      by_contra h
      apply hi0
      apply Fin.ext
      simp only [Fin.val_zero]
      omega
    have hn : i.val<edgeCount c := by
      by_contra h
      apply hin
      apply Fin.ext
      simp only [Fin.val_last]
      omega
    let j : Fin (edgeCount c+1) := ⟨i.val-1,by omega⟩
    let k : Fin (edgeCount c+1) := ⟨i.val+1,by omega⟩
    have hj : (rawGraph m r p).Adj (vertex c i) (vertex c j) :=
      ((freeComponentOrder m r p c).adjacent_iff _ _).2 (Or.inr (Or.inl (by dsimp [j]; omega)))
    have hk : (rawGraph m r p).Adj (vertex c i) (vertex c k) :=
      ((freeComponentOrder m r p c).adjacent_iff _ _).2 (Or.inl rfl)
    have hne : vertex c j≠vertex c k := by
      intro h
      have hh := congrArg Fin.val (vertex_injective c h)
      dsimp [j,k] at hh
      omega
    exact domain_of_two_base_gates hp hj hk hne (x i) (x j) (x k) (he i j hj) (he i k hk)

def ConsecutiveBaseAllowed {m r p : ℕ} (c : Component m r p) (x : Fin (edgeCount c+1)→State) : Prop :=
  (∀ j : Fin (edgeCount c),BaseAllowed r p (vertex c j.castSucc) (vertex c j.succ) (x j.castSucc) (x j.succ)) ∧
  ((freeComponentOrder m r p c).cycle=true →
    BaseAllowed r p (vertex c (Fin.last _)) (vertex c 0) (x (Fin.last _)) (x 0))

lemma consecutive_base_iff_all {m r p : ℕ} (c : Component m r p) (x : Fin (edgeCount c+1)→State) :
    ConsecutiveBaseAllowed c x ↔ AllBaseAllowed c x := by
  constructor
  · rintro ⟨hpath,hclose⟩ i j he
    have hh := ((freeComponentOrder m r p c).adjacent_iff i j).mp he
    rcases hh with hij | hji | ⟨hc,hh⟩
    · have hi : i.val<edgeCount c := by have := j.isLt; omega
      have hi' : i=Fin.castSucc (⟨i.val,hi⟩ : Fin (edgeCount c)) := Fin.ext rfl
      have hj' : j=Fin.succ (⟨i.val,hi⟩ : Fin (edgeCount c)) := Fin.ext hij.symm
      simpa only [← hi',← hj'] using hpath ⟨i.val,hi⟩
    · have hj : j.val<edgeCount c := by have := i.isLt; omega
      have hj' : j=Fin.castSucc (⟨j.val,hj⟩ : Fin (edgeCount c)) := Fin.ext rfl
      have hi' : i=Fin.succ (⟨j.val,hj⟩ : Fin (edgeCount c)) := Fin.ext hji.symm
      apply (baseAllowed_symm _ _ _ _).mpr
      simpa only [← hi',← hj'] using hpath ⟨j.val,hj⟩
    · rcases hh with ⟨hi,hj⟩ | ⟨hj,hi⟩
      · have hi' : i=0 := Fin.ext hi
        have hj' : j=Fin.last (edgeCount c) := Fin.ext hj
        rw [hi',hj']
        exact (baseAllowed_symm _ _ _ _).mpr (hclose hc)
      · have hi' : i=Fin.last (edgeCount c) := Fin.ext hi
        have hj' : j=0 := Fin.ext hj
        rw [hi',hj']
        exact hclose hc
  · intro h
    exact ⟨fun j => h _ _ (consecutive_adj c j),fun hc => h _ _ (closing_adj c hc)⟩

/-- Exact elimination of every internal unary alphabet and self-pair mask.
The complete physical source is endpoint tests plus the actual D/E/C gates. -/
theorem allowed_iff_boundary_base {m r p : ℕ} (hp : Parameters m r p 4)
    (c : Component m r p) (x : Fin (edgeCount c+1)→State) :
    Allowed c x ↔ BoundaryAllowed c x ∧ ConsecutiveBaseAllowed c x := by
  constructor
  · rintro ⟨hu,hpath,hclose⟩
    refine ⟨fun _ => ⟨hu 0,hu (Fin.last _)⟩,?_,?_⟩
    · intro j
      exact (baseAllowed_iff_of_domains hp c _ _ (consecutive_adj c j) _ _
        (hu j.castSucc) (hu j.succ)).mpr (hpath j)
    · intro hc
      exact (baseAllowed_iff_of_domains hp c _ _ (closing_adj c hc) _ _
        (hu (Fin.last _)) (hu 0)).mpr (hclose hc)
  · rintro ⟨hb,he⟩
    refine ⟨all_base_implies_domains hp c x hb ((consecutive_base_iff_all c x).mp he),?_,?_⟩
    · intro j
      exact baseAllowed_bound hp (consecutive_adj c j) _ _ (he.1 j)
    · intro hc
      exact baseAllowed_bound hp (closing_adj c hc) _ _ (he.2 hc)

end SubmittedGenus.CapFourMass.ActualComponent
