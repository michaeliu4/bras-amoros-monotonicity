import Results.Genus.Injection.ReservoirSources.DecoratedMarked
import Results.Genus.FiniteArithmetic.Reservoir.FailureOperator

noncomputable section
namespace SubmittedGenus.FiniteArithmetic.Reservoir
open OriginalReservoir PowerSeries
open scoped BigOperators
attribute [local instance] Classical.propDecidable
set_option synthInstance.maxSize 4000

/-- Split total weight between a literal marked code and its decorations. -/
def weightDecorationEquiv {M : Type} (D : Decoration) (w d : M→ℕ) (g : ℕ) :
    {x : (Σm:M,Fin (d m)→D.Letter) // w x.1+(∑i,D.weight (x.2 i))=g} ≃
      (Σ n:Fin (g+1), Σ m:{m:M // w m=n.val}, D.Atoms (d m.val) (g-n.val)) where
  toFun x := ⟨⟨w x.val.1,by have := x.property; omega⟩,⟨x.val.1,rfl⟩,
    ⟨x.val.2,by have := x.property; change (∑i,D.weight (x.val.2 i))=g-w x.val.1; omega⟩⟩
  invFun x := ⟨⟨x.2.1.val,x.2.2.val⟩,by
    have hn := x.1.isLt
    have hw := x.2.1.property
    have hf := x.2.2.property
    change (∑i,D.weight (x.2.2.val i))=g-x.1.val at hf
    change w x.2.1.val+(∑i,D.weight (x.2.2.val i))=g
    omega⟩
  left_inv _ := rfl
  right_inv x := by
    rcases x with ⟨⟨n,hn⟩,⟨m,hm⟩,⟨f,hf⟩⟩
    dsimp at hm
    subst n
    rfl

/-- Actual physical occurrences with exactly one independent decoration
for each unit of distance, partitioned by undecorated prefix weight. -/
abbrev DecoratedOccurrenceAt {C : Type} (F : PrefixFamily C) (D : Decoration) (g : ℕ) :=
  Σ n:Fin (g+1), Σ p:PrefixOccurrence F n.val, D.Atoms p.distance (g-n.val)

def physicalDecorationEquiv {M C : Type} (D : Decoration) (F : PrefixFamily C)
    (w d : M→ℕ) (e : ∀n,{m:M // w m=n} ≃ PrefixOccurrence F n)
    (hd : ∀n m,(e n m).distance=d m.val) (g : ℕ) :
    (Σ n:Fin (g+1), Σ m:{m:M // w m=n.val}, D.Atoms (d m.val) (g-n.val)) ≃
      DecoratedOccurrenceAt F D g :=
  Equiv.sigmaCongrRight (fun n => Equiv.sigmaCongr (e n.val)
    (fun m => Equiv.cast (congrArg (fun k => D.Atoms k (g-n.val)) (hd n.val m).symm)))

def safeMarkedDecoratedEquiv (D : Decoration) (g : ℕ) :
    SafeMarkedSource D g ≃ DecoratedOccurrenceAt safeFamily D g :=
  ((safeMarkedPresentation D).equiv g).trans
    ((weightDecorationEquiv D (fun m:SafeMarkedCode => m.prefix.weight)
      (fun m => m.split.after.length) g).trans
        (physicalDecorationEquiv D safeFamily (fun m:SafeMarkedCode => m.prefix.weight)
          (fun m => m.split.after.length) safeMarkedPrefixEquiv
          safeMarkedPrefixEquiv_distance g))

def earlyMarkedDecoratedEquiv (D : Decoration) (g : ℕ) :
    EarlyMarkedSource D g ≃ DecoratedOccurrenceAt earlyFamily D g :=
  ((earlyMarkedPresentation D).equiv g).trans
    ((weightDecorationEquiv D (fun m:EarlyMarkedCode => m.prefix.weight)
      (fun m => m.split.after.length) g).trans
        (physicalDecorationEquiv D earlyFamily (fun m:EarlyMarkedCode => m.prefix.weight)
          (fun m => m.split.after.length) earlyMarkedPrefixEquiv
          earlyMarkedPrefixEquiv_distance g))

/-- The exact coefficient form of F_s(z,t) at a finite decoration series t. -/
lemma safeMarkedSeries_physical_coeff (D : Decoration) (g : ℕ) :
    coeff g (safeMarkedSeries D)=
      ∑ n:Fin (g+1), ∑ p:PrefixOccurrence safeFamily n.val,
        coeff (g-n.val) (D.series^p.distance) := by
  rw [safeMarkedSeries,Graded.coeff_series,Fintype.card_congr (safeMarkedDecoratedEquiv D g)]
  simp only [DecoratedOccurrenceAt,Fintype.card_sigma,Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro n _
  apply Finset.sum_congr rfl
  intro p _
  rw [←D.atoms_series p.distance,Graded.coeff_series]

/-- The exact coefficient form of F_e(z,t), with every occurrence retained. -/
lemma earlyMarkedSeries_physical_coeff (D : Decoration) (g : ℕ) :
    coeff g (earlyMarkedSeries D)=
      ∑ n:Fin (g+1), ∑ p:PrefixOccurrence earlyFamily n.val,
        coeff (g-n.val) (D.series^p.distance) := by
  rw [earlyMarkedSeries,Graded.coeff_series,Fintype.card_congr (earlyMarkedDecoratedEquiv D g)]
  simp only [DecoratedOccurrenceAt,Fintype.card_sigma,Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro n _
  apply Finset.sum_congr rfl
  intro p _
  rw [←D.atoms_series p.distance,Graded.coeff_series]

#print axioms safeMarkedDecoratedEquiv
#print axioms earlyMarkedDecoratedEquiv
#print axioms safeMarkedSeries_physical_coeff
#print axioms earlyMarkedSeries_physical_coeff


/-- The graded safe grammar is exactly the physical marked-prefix series,
for every finite decoration alphabet, including t=1 and t=c. -/
lemma safeMarkedSeries_eq_physical (D : Decoration) :
    safeMarkedSeries D=markedPrefixSeries safeFamily D.series := by
  apply PowerSeries.ext
  intro g
  rw [safeMarkedSeries_physical_coeff,markedPrefixSeries,gradedTransform_coeff]
  simp only [map_sum]

/-- The analogous exact physical identification for the early-single-one family. -/
lemma earlyMarkedSeries_eq_physical (D : Decoration) :
    earlyMarkedSeries D=markedPrefixSeries earlyFamily D.series := by
  apply PowerSeries.ext
  intro g
  rw [earlyMarkedSeries_physical_coeff,markedPrefixSeries,gradedTransform_coeff]
  simp only [map_sum]

#print axioms safeMarkedSeries_eq_physical
#print axioms earlyMarkedSeries_eq_physical
end SubmittedGenus.FiniteArithmetic.Reservoir
