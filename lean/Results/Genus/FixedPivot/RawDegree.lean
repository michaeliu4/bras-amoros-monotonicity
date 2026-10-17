import Results.Genus.RawGraph
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-! The original fixed-pivot raw-polynomial degree bound, from actual source alphabets. -/
namespace SubmittedGenus.FixedPivot
open RawGraph
open scoped BigOperators

/-- Every physical vertex contributes once; the two fixed pivots contribute8,
the r−1 earlier coordinates cost at most4, and all other free ones at most3. -/
theorem raw_cap_four_genus_upper {m r p : ℕ} {x : Word m}
    (h : RawAdmissible r p 4 x) : genus x ≤ 3*m+r-2 := by
  have hr:=h.1.1
  have hrp:=h.1.2.1
  have hpm:=h.1.2.2.1
  let ri : Fin (m-1) := ⟨r-1,by omega⟩
  let pi : Fin (m-1) := ⟨p-1,by omega⟩
  have eri : physical ri=r := by dsimp [physical,ri]; omega
  have epi : physical pi=p := by dsimp [physical,pi]; omega
  have hne : ri≠pi := by intro he; have:=congrArg physical he; omega
  have hbefore : (∑ i : Fin (m-1), if physical i<r then 1 else 0)=r-1 := by
    have he : ∀ i : Fin (m-1), physical i<r ↔ i.val<r-1 := by
      intro i
      dsimp [physical]
      omega
    simp_rw [he]
    rw [Finset.sum_boole,Fin.card_filter_val_lt]
    exact min_eq_right (by omega)
  have hb : ∀ i : Fin (m-1), x i ≤
      3+(if physical i<r then 1 else 0)+(if i=ri then 1 else 0)+(if i=pi then 1 else 0) := by
    intro i
    by_cases hir : i=ri
    · subst i
      have hx:=alphabet_pivot h.2.1 (Or.inl eri)
      simp only [hx,if_pos rfl,if_neg hne]
      split_ifs <;> omega
    by_cases hip : i=pi
    · subst i
      have hx:=alphabet_pivot h.2.1 (Or.inr epi)
      simp only [hx,if_pos rfl,if_neg hir]
      split_ifs <;> omega
    · have hfree : ¬IsPivot r p i := by
        rintro (hri | hpi)
        · apply hir
          apply Fin.ext
          dsimp [physical,ri] at *
          omega
        · apply hip
          apply Fin.ext
          dsimp [physical,pi] at *
          omega
      have hh:=h.2.1 i
      simp only [hfree,if_false] at hh
      simp only [if_neg hir,if_neg hip]
      split_ifs at hh ⊢ <;> omega
  have hsum:=Finset.sum_le_sum (s := Finset.univ) (fun i _ => hb i)
  have he : (∑ i : Fin (m-1),
      (3+(if physical i<r then 1 else 0)+(if i=ri then 1 else 0)+(if i=pi then 1 else 0))) =
      (m-1)*3+(r-1)+1+1 := by
    simp [Finset.sum_add_distrib,hbefore]
  rw [he] at hsum
  change genus x ≤ (m-1)*3+(r-1)+1+1 at hsum
  omega

/-- This is a complete source-polynomial degree theorem, not an enumerator cutoff premise. -/
theorem raw_cap_four_natDegree (m r p : ℕ) :
    (rawPolynomial m r p 4).natDegree ≤ 3*m+r-2 := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro g hg
  rw [rawPolynomial_coeff]
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨_, hx, hgen⟩:=Finset.mem_filter.mp hx
  have hu:=raw_cap_four_genus_upper hx
  omega

end SubmittedGenus.FixedPivot
