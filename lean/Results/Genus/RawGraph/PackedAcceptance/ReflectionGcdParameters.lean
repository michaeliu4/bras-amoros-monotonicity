import Results.Genus.RawGraph.PackedAcceptance.ModularReflection
import Results.Genus.RawGraph.Layout

/-! Executable gcd coordinates for the original two-pivot reflection graph,
and exact physical-layout transport back to the original multiplicity. -/
namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionGcdParameters
open LayoutCompiler SourceModel

def gcdScale (M r p : ℕ) : ℕ := Nat.gcd M (p-r)
def orbitLength (M r p : ℕ) : ℕ := M/gcdScale M r p
def reducedGap (M r p : ℕ) : ℕ := (p-r)/gcdScale M r p

lemma gcdScale_pos {M r p : ℕ} (hM : 0<M) : 0<gcdScale M r p :=
  Nat.gcd_pos_of_pos_left (p-r) hM

lemma modulus_eq (M r p : ℕ) : M=gcdScale M r p*orbitLength M r p :=
  (Nat.mul_div_cancel' (Nat.gcd_dvd_left M (p-r))).symm

lemma gap_eq (M r p : ℕ) : p-r=gcdScale M r p*reducedGap M r p :=
  (Nat.mul_div_cancel' (Nat.gcd_dvd_right M (p-r))).symm

lemma reducedGap_pos {M r p : ℕ} (hrp : r<p) : 0<reducedGap M r p := by
  have hgap : 0<p-r := by omega
  have he:=gap_eq M r p
  by_contra h
  have hz : reducedGap M r p=0 := by omega
  rw [hz,Nat.mul_zero] at he
  omega

lemma reducedGap_lt {M r p : ℕ} (hp : p<M) : reducedGap M r p<orbitLength M r p := by
  have hgap : p-r<M := by omega
  rw [modulus_eq M r p,gap_eq M r p] at hgap
  exact Nat.lt_of_mul_lt_mul_left hgap

lemma orbitLength_two {M r p : ℕ} (hrp : r<p) (hp : p<M) : 2≤orbitLength M r p := by
  have hpos:=reducedGap_pos (M:=M) hrp
  have hlt:=reducedGap_lt (r:=r) hp
  omega

lemma reducedGap_coprime {M r p : ℕ} (hM : 0<M) :
    Nat.Coprime (reducedGap M r p) (orbitLength M r p) := by
  exact (Nat.coprime_div_gcd_div_gcd (m:=M) (n:=p-r) (gcdScale_pos hM)).symm

/-- The actual reduced pivot gap is a unit, built by the computable ZMod API. -/
def gapUnit (M r p : ℕ) (hM : 0<M) : (ZMod (orbitLength M r p))ˣ :=
  ZMod.unitOfCoprime (reducedGap M r p) (reducedGap_coprime hM)

@[simp] lemma gapUnit_coe (M r p : ℕ) (hM : 0<M) :
    (gapUnit M r p hM : ZMod (orbitLength M r p))=(reducedGap M r p:ℕ) := rfl

/-- All reduced coordinates needed by the source reflection families. -/
theorem original_parameters {M r p a : ℕ} (hp : Parameters M r p a) :
    0<gcdScale M r p ∧ 2≤orbitLength M r p ∧
      0<reducedGap M r p ∧ reducedGap M r p<orbitLength M r p ∧
      M=gcdScale M r p*orbitLength M r p ∧
      p-r=gcdScale M r p*reducedGap M r p ∧
      Nat.Coprime (reducedGap M r p) (orbitLength M r p) := by
  have hM : 0<M := by have:=hp.1; have:=hp.2.1; have:=hp.2.2.1; omega
  exact ⟨gcdScale_pos hM,orbitLength_two hp.2.1 hp.2.2.1,reducedGap_pos hp.2.1,
    reducedGap_lt hp.2.2.1,modulus_eq M r p,gap_eq M r p,reducedGap_coprime hM⟩

/-- Only the multiplicity index is transported. Component order, edge count,
cycle flags and every physical natural-number coordinate are unchanged. -/
def transportLayout {M m : ℕ} (hm : M=m) (L : Layout m) : Layout M where
  count := L.count
  edges := L.edges
  cycle := L.cycle
  label := L.label.trans (finCongr (congrArg (fun n : ℕ => n-1) hm.symm))

@[simp] lemma transportLayout_count {M m : ℕ} (hm : M=m) (L : Layout m) :
    (transportLayout hm L).count=L.count := rfl
@[simp] lemma transportLayout_edges {M m : ℕ} (hm : M=m) (L : Layout m) :
    (transportLayout hm L).edges=L.edges := rfl
@[simp] lemma transportLayout_cycle {M m : ℕ} (hm : M=m) (L : Layout m) :
    (transportLayout hm L).cycle=L.cycle := rfl
@[simp] lemma transportLayout_label_val {M m : ℕ} (hm : M=m) (L : Layout m) (v : L.Vertex) :
    ((transportLayout hm L).label v).val=(L.label v).val := rfl
@[simp] lemma transportLayout_physical {M m : ℕ} (hm : M=m) (L : Layout m) (v : L.Vertex) :
    physical ((transportLayout hm L).label v)=physical (L.label v) := rfl

@[simp] lemma transportLayout_domain {M m : ℕ} (hm : M=m) (L : Layout m)
    (r p a : ℕ) (v : L.Vertex) (x : ℕ) :
    Domain r p a ((transportLayout hm L).label v) x ↔ Domain r p a (L.label v) x := by
  subst M
  rfl

@[simp] lemma transportLayout_edgeBound {M m : ℕ} (hm : M=m) (L : Layout m)
    (r p a : ℕ) (u v : L.Vertex) :
    edgeBound r p a ((transportLayout hm L).label u) ((transportLayout hm L).label v)=
      edgeBound r p a (L.label u) (L.label v) := by
  subst M
  rfl

@[simp] lemma transportLayout_covers {M m : ℕ} (hm : M=m) (L : Layout m) (r p a : ℕ) :
    Covers (transportLayout hm L) r p a ↔ Covers L r p a := by
  subst M
  rfl

@[simp] lemma transportLayout_componentAllowed {M m : ℕ} (hm : M=m) (L : Layout m)
    (r p a : ℕ) (c : Fin L.count) (x : Fin (L.edges c+1)→Fin (a+1)) :
    ComponentAllowed (transportLayout hm L) r p a c x ↔ ComponentAllowed L r p a c x := by
  subst M
  rfl

@[simp] lemma transportLayout_componentRun {M m : ℕ} (hm : M=m) (L : Layout m)
    (r p a : ℕ) (c : Fin L.count) :
    componentRun (transportLayout hm L) r p a c=componentRun L r p a c := by
  subst M
  rfl

/-- Apply an actual gcd-coset layout at the original submitted multiplicity. -/
def originalLayout (M r p : ℕ)
    (L : Layout (gcdScale M r p*orbitLength M r p)) : Layout M :=
  transportLayout (modulus_eq M r p) L

lemma originalLayout_covers (M r p a : ℕ)
    (L : Layout (gcdScale M r p*orbitLength M r p)) (hL : Covers L r p a) :
    Covers (originalLayout M r p L) r p a :=
  (transportLayout_covers (modulus_eq M r p) L r p a).mpr hL

end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionGcdParameters
