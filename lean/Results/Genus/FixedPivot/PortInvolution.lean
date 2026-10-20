import Results.Genus.FixedPivot.PathGeometry

/-! The actual canonical port pairing, unchanged on multiplicity progressions. -/
namespace SubmittedGenus.FixedPivot

namespace ResiduePair
variable {N d : ℕ}

/-- The source endpoint identity determines the paired port and common length uniquely. -/
lemma determined_by_a (L M : ResiduePair N d) (ha : L.a=M.a) :
    L.b=M.b ∧ L.n=M.n := by
  have hL:=L.endpoint
  have hM:=M.endpoint
  have hLn:=L.n_pos
  have hMn:=M.n_pos
  have he : L.b+(L.n-1)*d=M.b+(M.n-1)*d := by omega
  obtain ⟨hb,hn⟩ := residue_list_unique L.b_pos L.b_le M.b_pos M.b_le he
  exact ⟨hb,by omega⟩

end ResiduePair

/-- Port labels are1,...,d while the Lean index is0,...,d−1. -/
def pairForPort (N d : ℕ) (hN : d<N) (a : Fin d) : ResiduePair N d :=
  residuePair N d (a.val+1) (by have:=a.isLt; omega) (by omega)
    (by have:=a.isLt; omega) (by have:=a.isLt; omega)

/-- The source reflection induces an actual involution on all port classes. -/
def portPartner (N d : ℕ) (hN : d<N) (a : Fin d) : Fin d :=
  ⟨(pairForPort N d hN a).b-1, by
    have hb:=(pairForPort N d hN a).b_pos
    have hd:=(pairForPort N d hN a).b_le
    omega⟩

lemma portPartner_val (N d : ℕ) (hN : d<N) (a : Fin d) :
    (portPartner N d hN a).val+1=(pairForPort N d hN a).b := by
  have hb:=(pairForPort N d hN a).b_pos
  unfold portPartner
  dsimp only
  omega

/-- Reflection exchanges the two lists and preserves their common length. -/
lemma pairForPort_partner (N d : ℕ) (hN : d<N) (a : Fin d) :
    (pairForPort N d hN (portPartner N d hN a)).b=a.val+1 ∧
      (pairForPort N d hN (portPartner N d hN a)).n=(pairForPort N d hN a).n := by
  let L:=pairForPort N d hN a
  let M:=pairForPort N d hN (portPartner N d hN a)
  have hma : M.a=L.b := portPartner_val N d hN a
  have hh:=ResiduePair.determined_by_a M L.swap hma
  exact hh

theorem portPartner_involutive (N d : ℕ) (hN : d<N) :
    Function.Involutive (portPartner N d hN) := by
  intro a
  apply Fin.ext
  have hh:=(pairForPort_partner N d hN a).1
  have hv:=portPartner_val N d hN (portPartner N d hN a)
  omega

/-- Increasing N by d preserves every port pair and increments every list length once. -/
theorem pairForPort_progression (N d : ℕ) (hN : d<N) (a : Fin d) :
    (pairForPort (N+d) d (by omega) a).b=(pairForPort N d hN a).b ∧
      (pairForPort (N+d) d (by omega) a).n=(pairForPort N d hN a).n+1 := by
  exact ResiduePair.determined_by_a (pairForPort (N+d) d (by omega) a)
    (pairForPort N d hN a).extend rfl

theorem portPartner_progression (N d : ℕ) (hN : d<N) :
    portPartner (N+d) d (by omega)=portPartner N d hN := by
  funext a
  apply Fin.ext
  have hh:=(pairForPort_progression N d hN a).1
  simp only [portPartner,hh]

end SubmittedGenus.FixedPivot
