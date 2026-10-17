import Results.Genus.RawGraph.PackedAcceptance.MaterializedVectorProduct

/-! A source step stores only its finite mask and threshold. The vector action
uses finite sums and one monomial multiplication per allowed state, never a
materialized matrix. Ordered words act from their rightmost suffix. -/
namespace SubmittedGenus.RawGraph.PackedAcceptance.CachedStepAction
open CompressedSignature MaterializedMatrixMonoid
open scoped BigOperators Matrix

structure CachedStep (k : ℕ) where
  mask : List.Vector Bool k
  bound : ℕ
  deriving DecidableEq

def cache {k : ℕ} (s : Step k) : CachedStep k := ⟨List.Vector.ofFn s.mask,s.bound⟩
def uncache {k : ℕ} (s : CachedStep k) : Step k := ⟨s.mask.get,s.bound⟩
@[simp] lemma uncache_cache {k : ℕ} (s : Step k) : uncache (cache s)=s := by
  cases s with
  | mk m b =>
    unfold uncache cache
    congr 1
    funext i
    exact List.Vector.get_ofFn m i

section Semiring
variable {k : ℕ} {R : Type*} [CommSemiring R]

def powers (z : R) : List.Vector R k := List.Vector.ofFn (fun i : Fin k=>z^i.val)

def admittedSum (s : CachedStep k) (v : List.Vector R k) (i : Fin k) : R :=
  (List.ofFn (fun j : Fin k=>if s.bound ≤ i.val+j.val then v.get j else 0)).sum

def action (p : List.Vector R k) (s : CachedStep k) (v : List.Vector R k) : List.Vector R k :=
  List.Vector.ofFn (fun i=>if s.mask.get i then p.get i * admittedSum s v i else 0)

lemma action_eq (z : R) (s : CachedStep k) (v : List.Vector R k) :
    (fun i=>(action (powers z) s v).get i)=stepMatrix z (uncache s) *ᵥ (fun i=>v.get i) := by
  funext i
  simp only [action,List.Vector.get_ofFn,powers,admittedSum,List.sum_ofFn,
    Matrix.mulVec,dotProduct,stepMatrix,uncache]
  split_ifs with hm
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp
  · simp

/-- Every suffix is evaluated once, in source order. -/
def run (p : List.Vector R k) : List (CachedStep k) → List.Vector R k → List.Vector R k
  | [],v => v
  | s::w,v => action p s (run p w v)

lemma run_eq (z : R) (w : List (CachedStep k)) (v : List.Vector R k) :
    (fun i=>(run (powers z) w v).get i)=
      ((w.map (fun s=>stepMatrix z (uncache s))).prod) *ᵥ (fun i=>v.get i) := by
  induction w with
  | nil => simp [run]
  | cons s w ih =>
    simp only [run,List.map_cons,List.prod_cons]
    rw [action_eq,ih,Matrix.mulVec_mulVec]

lemma run_source (z : R) (w : List (Step k)) (v : List.Vector R k) :
    (fun i=>(run (powers z) (w.map cache) v).get i)=
      (w.map (stepMatrix z)).prod *ᵥ (fun i=>v.get i) := by
  rw [run_eq,List.map_map]
  simp only [Function.comp_def,uncache_cache]

/-- Terminal masks and actual-first closure remain explicit cached data. -/
structure Terminal (k : ℕ) where
  mask : List.Vector Bool k
  cycle : Bool
  close : ℕ

def cacheTerminal {cap : ℕ} (s : ComponentSignature cap) : Terminal (cap+1) :=
  ⟨List.Vector.ofFn (s.mask ⟨s.edges,by omega⟩),s.cycle,s.close⟩

def finish (p : List.Vector R k) (t : Terminal k) (first : Fin k) : List.Vector R k :=
  List.Vector.ofFn (fun last=>if t.mask.get last then
    if t.cycle && decide (t.close≤last.val+first.val) || !t.cycle then p.get last else 0 else 0)

lemma finish_eq {cap : ℕ} (s : ComponentSignature cap) (z : R) (first : Fin (cap+1)) :
    (fun last=>(finish (powers z) (cacheTerminal s) first).get last)=terminal s z first := by
  funext last
  simp only [finish,powers,cacheTerminal,List.Vector.get_ofFn,terminal,signatureVertices]
  simp only [show s.edges<s.edges+1 by omega,↓reduceDIte]
  split_ifs <;> simp_all

def vectorSum (v : List.Vector R k) : R := (List.ofFn v.get).sum

/-- Open paths share one suffix vector; cycles retain their actual first-state
terminal gate and run one vector per first state. -/
def value {cap : ℕ} (p : List.Vector R (cap+1))
    (w : List (CachedStep (cap+1))) (t : Terminal (cap+1)) : R :=
  if t.cycle then
    (List.ofFn (fun first=>(run p w (finish p t first)).get first)).sum
  else vectorSum (run p w (finish p t 0))

lemma value_eq {cap : ℕ} (s : ComponentSignature cap) (z : R)
    (w : List (CachedStep (cap+1))) (hw : w=(sourceSteps s).map cache) :
    value (powers z) w (cacheTerminal s)=signatureScalar s z := by
  subst w
  rw [←matrixValue_eq_signature s z]
  unfold value
  split_ifs with hc
  · simp only [cacheTerminal] at hc
    simp only [List.sum_ofFn,matrixValue]
    apply Finset.sum_congr rfl
    intro first _
    have hr:=congrFun (run_source z (sourceSteps s) (finish (powers z) (cacheTerminal s) first)) first
    rw [finish_eq] at hr
    exact hr
  · simp only [cacheTerminal] at hc
    simp only [vectorSum,List.sum_ofFn,matrixValue]
    apply Finset.sum_congr rfl
    intro first _
    have hr:=congrFun (run_source z (sourceSteps s) (finish (powers z) (cacheTerminal s) 0)) first
    rw [finish_eq] at hr
    have ht : terminal s z (0:Fin (cap+1))=terminal s z first := by
      funext last;simp [terminal,hc]
    simpa only [ht] using hr
end Semiring

/-- At a power-of-two base, each monomial action is an actual bit shift. -/
def actionBits {k : ℕ} (bits : ℕ) (s : CachedStep k) (v : List.Vector ℕ k) : List.Vector ℕ k :=
  List.Vector.ofFn (fun i=>if s.mask.get i then (admittedSum s v i) <<< (bits*i.val) else 0)

lemma actionBits_eq {k : ℕ} (bits : ℕ) (s : CachedStep k) (v : List.Vector ℕ k) :
    actionBits bits s v=action (powers (2^bits)) s v := by
  apply List.Vector.ext
  intro i
  simp [actionBits,action,powers,Nat.shiftLeft_eq,pow_mul,Nat.mul_comm]

def runBits {k : ℕ} (bits : ℕ) : List (CachedStep k) → List.Vector ℕ k → List.Vector ℕ k
  | [],v => v
  | s::w,v => actionBits bits s (runBits bits w v)

lemma runBits_eq {k : ℕ} (bits : ℕ) (w : List (CachedStep k)) (v : List.Vector ℕ k) :
    runBits bits w v=run (powers (2^bits)) w v := by
  induction w with
  | nil => rfl
  | cons s w ih => simp only [runBits,run,ih,actionBits_eq]

def valueBits {cap : ℕ} (bits : ℕ) (w : List (CachedStep (cap+1))) (t : Terminal (cap+1)) : ℕ :=
  let p:=powers (2^bits)
  if t.cycle then (List.ofFn (fun first=>(runBits bits w (finish p t first)).get first)).sum
  else vectorSum (runBits bits w (finish p t 0))

lemma valueBits_eq {cap : ℕ} (bits : ℕ) (s : ComponentSignature cap)
    (w : List (CachedStep (cap+1))) (hw : w=(sourceSteps s).map cache) :
    valueBits bits w (cacheTerminal s)=signatureScalar s (2^bits:ℕ) := by
  simpa only [valueBits,runBits_eq,value] using value_eq s (2^bits:ℕ) w hw

#print axioms action_eq
#print axioms run_source
#print axioms finish_eq
#print axioms value_eq
#print axioms actionBits_eq
#print axioms valueBits_eq
end SubmittedGenus.RawGraph.PackedAcceptance.CachedStepAction
