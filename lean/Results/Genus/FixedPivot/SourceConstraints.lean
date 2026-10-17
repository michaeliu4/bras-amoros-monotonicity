import Results.Genus.FixedPivot.TailLayout
import Results.Genus.RawGraph.SourceModel

/-! Exact original cap-four alphabets and thresholds for the core/tail split. -/
namespace SubmittedGenus.FixedPivot
open SubmittedGenus.RawGraph SubmittedGenus.RawGraph.SourceModel

/-- Above p, every physical coordinate is a free three-color carry coordinate;
the only unary reduction is the original carried-loop restriction. -/
theorem tail_domain_iff {m r p : ℕ} (hrp : r<p) (i : Fin (m-1))
    (hi : p<physical i) (v : ℕ) :
    Domain r p 4 i v ↔ 1≤v ∧ v≤3 ∧ (CarryLoop r p i → 2≤v) := by
  have hf : IsFree r p i := by unfold IsFree IsPivot; omega
  have hs : ¬StrongLoop r p i := by unfold StrongLoop; omega
  have hu : upper r 4 i=3 := by unfold upper; rw [if_neg (by omega)]
  rw [domain_iff_unary]
  unfold Unary
  simp only [show ¬IsPivot r p i from hf,hf,false_implies,true_implies,true_and,hu,hs]
  constructor
  · rintro ⟨hv,hup,hloop⟩
    exact ⟨hv,hup,fun hl => by have := hloop hl; omega⟩
  · rintro ⟨hv,hup,hloop⟩
    exact ⟨hv,hup,fun hl => by have := hloop hl; omega⟩

/-- Ports strictly between r and p have the same three-color upper alphabet. -/
theorem surviving_port_upper {m r p : ℕ} (i : Fin (m-1))
    (hi : r<physical i ∧ physical i<p) :
    IsFree r p i ∧ upper r 4 i=3 := by
  constructor
  · unfold IsFree IsPivot
    omega
  · unfold upper
    rw [if_neg (by omega)]

/-- Every nonloop tail-tail binary constraint is exactly the source carry threshold3. -/
theorem tail_edgeBound {m r p : ℕ} (hrp : r<p) (i j : Fin (m-1))
    (hi : p<physical i) (hj : p<physical j) :
    edgeBound r p 4 i j=
      if i=j then 0 else
        if physical i+physical j=m+r ∨ physical i+physical j=m+p then 3 else 0 := by
  have hpi : ¬IsPivot r p i := by unfold IsPivot; omega
  have hpj : ¬IsPivot r p j := by unfold IsPivot; omega
  have hs : ¬(physical i+physical j=r ∨ physical i+physical j=p) := by omega
  unfold edgeBound
  simp only [hpi,hpj,false_or,hs,ite_false]

/-- A tail coordinate cannot meet a core coordinate at a strong target. -/
theorem tail_core_edgeBound {m r p : ℕ} (hrp : r<p) (i j : Fin (m-1))
    (hi : p<physical i) (hj : physical j≤p) :
    edgeBound r p 4 i j=
      if IsPivot r p j then 0 else
        if physical i+physical j=m+r ∨ physical i+physical j=m+p then 3 else 0 := by
  have hpi : ¬IsPivot r p i := by unfold IsPivot; omega
  have hij : i≠j := by intro h; subst j; omega
  have hs : ¬(physical i+physical j=r ∨ physical i+physical j=p) := by omega
  unfold edgeBound
  simp only [hpi,hij,false_or,or_false,hs,ite_false]

/-- The core has no carried incidences once the original source condition m>2p holds. -/
theorem core_no_carry {m r p : ℕ} (hmp : 2*p<m) (i j : Fin (m-1))
    (hi : physical i≤p) (hj : physical j≤p) :
    ¬(physical i+physical j=m+r ∨ physical i+physical j=m+p) := by omega

/-- Thus the core binary constraints are independent of m. -/
theorem core_edgeBound {m r p : ℕ} (hmp : 2*p<m) (i j : Fin (m-1))
    (hi : physical i≤p) (hj : physical j≤p) :
    edgeBound r p 4 i j=
      if IsPivot r p i ∨ IsPivot r p j ∨ i=j then 0 else
        if physical i+physical j=r ∨ physical i+physical j=p then 4 else 0 := by
  unfold edgeBound
  rw [if_neg (core_no_carry hmp i j hi hj)]

/-- Only the surviving carry ports can couple the core to a tail. -/
theorem core_tail_port {m r p : ℕ} (hrp : r<p) (i j : Fin (m-1))
    (hi : p<physical i) (hj : physical j≤p) (he : 0<edgeBound r p 4 i j) :
    r<physical j ∧ physical j<p := by
  rw [tail_core_edgeBound hrp i j hi hj] at he
  split_ifs at he with hp hc
  · omega
  · have hv:=i.isLt
    unfold physical at *
    have hnp : (j.val+1)≠p := by
      intro h
      apply hp
      exact Or.inr h
    constructor <;> omega
  · omega

end SubmittedGenus.FixedPivot
