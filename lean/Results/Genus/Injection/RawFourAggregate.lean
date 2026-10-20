import Results.Genus.Injection.RawFourSources

noncomputable section
open scoped BigOperators
namespace SubmittedGenus.OriginalPopulations.RawFourAggregate
open RawGraph
attribute [local instance] Classical.propDecidable

lemma genus_ofList (w : List ℕ) : genus (KunzWord.ofList w)=w.sum := by
  calc
    _ = (List.ofFn (KunzWord.ofList w)).sum := List.sum_ofFn.symm
    _ = w.sum := congrArg List.sum (KunzWord.ofFn_ofList w)

abbrev FixedAt (m r p g : ℕ) :=
  {x : Fin (m-1) → Fin 5 // RawAdmissible r p 4 (boundedWord x) ∧ genus (boundedWord x)=g}

abbrev AggregateAt (g : ℕ) :=
  (m : Fin (g+2)) × (r : Fin (g+2)) × (p : Fin (g+2)) × FixedAt m.val r.val p.val g

instance (m r p g : ℕ) : Fintype (FixedAt m r p g) := inferInstance

lemma fixed_card (m r p g : ℕ) : Fintype.card (FixedAt m r p g)=
    (rawPolynomial m r p 4).coeff g := by
  rw [rawPolynomial_coeff]
  exact Fintype.card_subtype _

lemma aggregate_card (g : ℕ) : Fintype.card (AggregateAt g)=
    ∑ m : Fin (g+2),∑ r : Fin (g+2),∑ p : Fin (g+2),
      (rawPolynomial m.val r.val p.val 4).coeff g := by
  simp only [AggregateAt,Fintype.card_sigma,fixed_card]

def pivotR {g : ℕ} (w : RawFourAt g) : ℕ := w.property.1.choose
def pivotP {g : ℕ} (w : RawFourAt g) : ℕ := w.property.1.choose_spec.choose
lemma pivots_raw {g : ℕ} (w : RawFourAt g) :
    RawAdmissible (pivotR w) (pivotP w) 4 (KunzWord.ofList w.val) :=
  w.property.1.choose_spec.choose_spec

lemma length_bound {g : ℕ} (w : RawFourAt g) : w.val.length+1<g+2 := by
  have hh := cap_four_genus_multiplicity (pivots_raw w)
  rw [genus_ofList,w.property.2] at hh
  omega

lemma pivots_bounds {g : ℕ} (w : RawFourAt g) : pivotR w<g+2 ∧ pivotP w<g+2 := by
  have hp := (pivots_raw w).1
  have hm := length_bound w
  exact ⟨by have := hp.2.1; have := hp.2.2.1; omega,by have := hp.2.2.1; omega⟩

def encode {g : ℕ} (w : RawFourAt g) : AggregateAt g :=
  ⟨⟨w.val.length+1,length_bound w⟩,⟨pivotR w,(pivots_bounds w).1⟩,
    ⟨pivotP w,(pivots_bounds w).2⟩,
    ⟨fun i => ⟨KunzWord.ofList w.val i,
      Nat.lt_succ_of_le (raw_coordinate_bounds (pivots_raw w) i).2⟩,
      pivots_raw w,(genus_ofList w.val).trans w.property.2⟩⟩

def literal {g : ℕ} (s : AggregateAt g) : List ℕ := List.ofFn (boundedWord s.2.2.2.val)

lemma literal_encode {g : ℕ} (w : RawFourAt g) : literal (encode w)=w.val := by
  change List.ofFn (KunzWord.ofList w.val)=w.val
  exact KunzWord.ofFn_ofList _

lemma encode_injective (g : ℕ) : Function.Injective (@encode g) := by
  intro w v he
  apply Subtype.ext
  simpa only [literal_encode] using congrArg literal he

/-- Every literal raw word is assigned once to its actual bounded pivot source.
This is the source bridge needed by the finite coefficient upper envelope. -/
theorem rawFourCount_le_aggregate (g : ℕ) : rawFourCount g ≤
    ∑ m : Fin (g+2),∑ r : Fin (g+2),∑ p : Fin (g+2),
      (rawPolynomial m.val r.val p.val 4).coeff g := by
  rw [←aggregate_card]
  exact Fintype.card_le_of_injective _ (encode_injective g)

lemma raw_ofFn {m r p : ℕ} {x : Word m} (h : RawAdmissible r p 4 x) :
    RawAdmissible r p 4 (KunzWord.ofList (List.ofFn x)) := by
  have hm : (List.ofFn x).length+1=m := by
    simp only [List.length_ofFn]
    have := h.1.2.2.1
    omega
  let idx : Fin ((List.ofFn x).length+1-1) → Fin (m-1) :=
    fun i => ⟨i.val,by have := i.isLt; omega⟩
  have hv (i : Fin ((List.ofFn x).length+1-1)) :
      KunzWord.ofList (List.ofFn x) i=x (idx i) := by
    change (List.ofFn x)[i.val]=x (idx i)
    rw [List.getElem_ofFn]
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [hm] using h.1
  · intro i
    change (if IsPivot r p i then KunzWord.ofList (List.ofFn x) i=4
      else 1≤KunzWord.ofList (List.ofFn x) i ∧ KunzWord.ofList (List.ofFn x) i≤
        if physical i<r then 4 else 4-1)
    rw [hv]
    exact h.2.1 (idx i)
  · intro i j hij
    rw [hv,hv]
    exact h.2.2.1 (idx i) (idx j) hij
  · intro i j hij
    rw [hv,hv]
    apply h.2.2.2 (idx i) (idx j)
    change i.val+1+(j.val+1)=m+r ∨ i.val+1+(j.val+1)=m+p
    change i.val+1+(j.val+1)=(List.ofFn x).length+1+r ∨
      i.val+1+(j.val+1)=(List.ofFn x).length+1+p at hij
    omega

def decode {g : ℕ} (s : AggregateAt g) : RawFourAt g :=
  ⟨literal s,⟨s.2.1.val,s.2.2.1.val,raw_ofFn s.2.2.2.property.1⟩,
    List.sum_ofFn.trans s.2.2.2.property.2⟩

lemma decode_injective (g : ℕ) : Function.Injective (@decode g) := by
  rintro ⟨m,r,p,x⟩ ⟨n,s,q,y⟩ he
  have hl := congrArg (fun w : RawFourAt g => w.val) he
  change List.ofFn (boundedWord x.val)=List.ofFn (boundedWord y.val) at hl
  have hlen := congrArg List.length hl
  simp only [List.length_ofFn] at hlen
  have hm := x.property.1.1.2.2.1
  have hn := y.property.1.1.2.2.1
  have hmn : m=n := Fin.ext (by omega)
  subst n
  have hxy : boundedWord x.val=boundedWord y.val := List.ofFn_inj.mp hl
  have hy : RawAdmissible s.val q.val 4 (boundedWord x.val) := hxy.symm ▸ y.property.1
  obtain ⟨hrs,hpq⟩ := raw_parameters_unique x.property.1 hy
  have hrs' : r=s := Fin.ext hrs
  have hpq' : p=q := Fin.ext hpq
  subst s
  subst q
  have hxye : x=y := by
    apply Subtype.ext
    funext i
    exact Fin.ext (congrFun hxy i)
  subst y
  rfl

/-- Exact literal-list population equals the sum of its distinct fixed-pivot
bounded source coefficients; the reverse map uses pivot uniqueness. -/
theorem rawFourCount_eq_aggregate (g : ℕ) : rawFourCount g =
    ∑ m : Fin (g+2),∑ r : Fin (g+2),∑ p : Fin (g+2),
      (rawPolynomial m.val r.val p.val 4).coeff g := by
  apply le_antisymm (rawFourCount_le_aggregate g)
  rw [←aggregate_card]
  exact Fintype.card_le_of_injective _ (decode_injective g)

#print axioms rawFourCount_eq_aggregate
#print axioms rawFourCount_le_aggregate
end SubmittedGenus.OriginalPopulations.RawFourAggregate
