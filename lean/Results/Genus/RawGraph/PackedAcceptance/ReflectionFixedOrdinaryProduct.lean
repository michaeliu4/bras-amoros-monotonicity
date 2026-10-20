import Results.Genus.RawGraph.PackedAcceptance.ReflectionFixedOrdinaryWord

/-! Source-exact fixed-path product interface for a shifted-prefix evaluator.
All boundary factors remain literal original source fields. -/
namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionFixedOrdinaryWord
open LayoutCompiler SourceModel ReflectionPairedOrbit ReflectionFullLayout
open ReflectionFixedPhase ReflectionFixedSourceWindow ReflectionFixedPhysicalLabels
open ReflectionThresholdWord CompressedSignature
open scoped Matrix
variable {g : ℕ} [NeZero g]

def headSteps (n r p δ cap : ℕ) (a : Fin g) (hfix : a=mate r a)
    (hc : Nat.Coprime δ (n+2)) (ha0 : a≠0) : List (Step (cap+1)) :=
  (List.range (ordinaryHead n (targetIndex n r δ a hfix hc))).map
    (stepAt (signature n r p δ cap a hfix hc ha0))

def bodyWord (n r δ : ℕ) (a : Fin g) (hfix : a=mate r a)
    (hc : Nat.Coprime δ (n+2)) : List Letter :=
  (List.range (ordinaryPairs n (targetIndex n r δ a hfix hc))).map
    (fun k=>reducedLetter (n+2) δ (cut g a.val r)
      ((δ*(orbitStart n (targetIndex n r δ a hfix hc)+k))%(n+2)))

def tailSteps (n r p δ cap : ℕ) (a : Fin g) (hfix : a=mate r a)
    (hc : Nat.Coprime δ (n+2)) (ha0 : a≠0) : List (Step (cap+1)) :=
  (List.range' (ordinaryTailStart n (targetIndex n r δ a hfix hc))
    (n+1-ordinaryTailStart n (targetIndex n r δ a hfix hc))).map
      (stepAt (signature n r p δ cap a hfix hc ha0))

lemma boundary_lengths (n r p δ cap : ℕ) (a : Fin g) (hfix : a=mate r a)
    (hc : Nat.Coprime δ (n+2)) (ha0 : a≠0) :
    (headSteps n r p δ cap a hfix hc ha0).length≤2 ∧
    (tailSteps n r p δ cap a hfix hc ha0).length≤1 := by
  simp only [headSteps,tailSteps,List.length_map,List.length_range,List.length_range']
  exact ⟨(ordinaryHead_bounds n _).2.1,(ordinaryTail_bounds n _).2⟩

theorem sourceSteps_word (n r p δ cap : ℕ) (hr : 0<r) (hδ : 0<δ)
    (hp : p=r+g*δ) (hpm : p<g*(n+2)) (a : Fin g) (hfix : a=mate r a)
    (hc : Nat.Coprime δ (n+2)) (ha0 : a≠0) :
    sourceSteps (signature n r p δ cap a hfix hc ha0)=
      headSteps n r p δ cap a hfix hc ha0 ++
      (bodyWord n r δ a hfix hc).flatMap (pairSteps cap) ++
      tailSteps n r p δ cap a hfix hc ha0 := by
  rw [sourceSteps_partition n r p δ cap hr hδ hp hpm a hfix hc ha0]
  simp only [headSteps,tailSteps,bodyWord,List.flatMap_map,Function.comp_def]
  congr 1
  congr 1
  apply List.flatMap_congr
  intro k _
  congr 1
  rw [affine_letter_reduced g (n+2) r δ a.val _ (NeZero.pos g) a.isLt,
    orbitStart_coordinate]
  rfl

def pairValue {M : Type*} [Monoid M] (f : Step (cap+1)→M) (q : Letter) : M :=
  ((pairSteps cap q).map f).prod

/-- Noncommutative factorization; neither boundary order nor pair order is
changed. The middle product is exactly the shifted-prefix API payload. -/
theorem sourceSteps_product {M : Type*} [Monoid M] (f : Step (cap+1)→M)
    (n r p δ : ℕ) (hr : 0<r) (hδ : 0<δ) (hp : p=r+g*δ) (hpm : p<g*(n+2))
    (a : Fin g) (hfix : a=mate r a) (hc : Nat.Coprime δ (n+2)) (ha0 : a≠0) :
    ((sourceSteps (signature n r p δ cap a hfix hc ha0)).map f).prod=
      ((headSteps n r p δ cap a hfix hc ha0).map f).prod *
      ((bodyWord n r δ a hfix hc).map (pairValue f)).prod *
      ((tailSteps n r p δ cap a hfix hc ha0).map f).prod := by
  rw [sourceSteps_word n r p δ cap hr hδ hp hpm a hfix hc ha0]
  simp [pairValue,List.map_append,List.prod_append,List.flatMap_def,List.prod_flatten,
    List.map_map,Function.comp_def,mul_assoc]
  all_goals rfl

section Matrix
variable {R : Type*} [CommSemiring R]

def value (n r p δ cap : ℕ) (a : Fin g) (hfix : a=mate r a)
    (hc : Nat.Coprime δ (n+2)) (ha0 : a≠0) (z : R)
    (body : Matrix (Fin (cap+1)) (Fin (cap+1)) R) : R :=
  matrixValue (signature n r p δ cap a hfix hc ha0) z
    (((headSteps n r p δ cap a hfix hc ha0).map (stepMatrix z)).prod * body *
      ((tailSteps n r p δ cap a hfix hc ha0).map (stepMatrix z)).prod)

/-- Only an ordered middle-product identity is required; actual first/last
masks and the literal unused closing field stay in the original signature. -/
theorem value_eq_signature (n r p δ cap : ℕ) (hr : 0<r) (hδ : 0<δ)
    (hp : p=r+g*δ) (hpm : p<g*(n+2)) (a : Fin g) (hfix : a=mate r a)
    (hc : Nat.Coprime δ (n+2)) (ha0 : a≠0) (z : R)
    (body : Matrix (Fin (cap+1)) (Fin (cap+1)) R)
    (hb : body=((bodyWord n r δ a hfix hc).map (pairValue (stepMatrix z))).prod) :
    value n r p δ cap a hfix hc ha0 z body=
      signatureScalar (signature n r p δ cap a hfix hc ha0) z := by
  unfold value
  rw [hb,←sourceSteps_product (stepMatrix z) n r p δ hr hδ hp hpm a hfix hc ha0]
  exact matrixValue_eq_signature _ z

/-- Original raw component scalar, obtained through the complete physical
signature equality, without finite geometry or per-position checks. -/
theorem source_scalar (n r p δ cap : ℕ) (hr : 0<r) (hδ : 0<δ)
    (hc : Nat.Coprime δ (n+2)) (hp : p=r+g*δ) (hp0 : 0<p) (hpm : p<g*(n+2))
    (c : Fin (count (g:=g) r)) (hfix : representative r c=mate r (representative r c))
    (ha0 : representative r c≠0) (z : R)
    (body : Matrix (Fin (cap+1)) (Fin (cap+1)) R)
    (hb : body=((bodyWord n r δ (representative r c) hfix hc).map (pairValue (stepMatrix z))).prod) :
    scalarComponent (layout n r p δ hc hp hp0 hpm) r p cap z c=
      value n r p δ cap (representative r c) hfix hc ha0 z body := by
  rw [scalarComponent_eq_signature,ReflectionFixedPhysicalLabels.physicalSignature_eq
    n r p δ cap hc hp hp0 hpm c hfix ha0]
  exact (value_eq_signature n r p δ cap hr hδ hp hpm (representative r c) hfix hc ha0 z body hb).symm
end Matrix

#print axioms sourceSteps_word
#print axioms sourceSteps_product
#print axioms source_scalar
end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionFixedOrdinaryWord
