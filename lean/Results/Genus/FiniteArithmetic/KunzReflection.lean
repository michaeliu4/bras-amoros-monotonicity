import Results.Genus.FiniteArithmetic.ReflectionConstraints
import Results.Genus.FiniteArithmetic.UnboundedTail
import Results.Genus.Injection.WordLists
import Results.Genus.Injection.Residual

namespace SubmittedGenus.FiniteArithmetic

open Reflection

/-- Physical coordinates strictly before the pivot p. -/
def leftBlock {m : ℕ} (x : KunzWord m) (p : ℕ) : List ℕ :=
  List.ofFn (fun i : Fin (p - 1) => KunzWord.coord x (i.val + 1))

/-- Physical coordinates strictly after the pivot p. -/
def rightBlock {m : ℕ} (x : KunzWord m) (p : ℕ) : List ℕ :=
  List.ofFn (fun i : Fin (m - p - 1) => KunzWord.coord x (p + i.val + 1))

/-- The left reflection constraints are literal noncarry Kunz inequalities. -/
theorem leftBlock_language {m p cap : ℕ} (x : KunzWord m) (hx : x.Valid)
    (hp : 0 < p) (hpm : p < m)
    (hcap : ∀ i, 0 < i → i < p → KunzWord.coord x i ≤ cap) :
    Language (boundedSystem (KunzWord.coord x p) cap).pairAllowed
      (boundedSystem (KunzWord.coord x p) cap).centerAllowed (leftBlock x p) := by
  apply ofFn_bounded_language
  · intro i
    have hi := i.isLt
    exact ⟨hx.coord_pos (by omega) (by omega), hcap _ (by omega) (by omega)⟩
  · intro i j hij
    have hi := i.isLt
    have hj := j.isLt
    have he : (i.val + 1) + (j.val + 1) = p := by omega
    have h := hx.noncarry (i.val + 1) (j.val + 1) (by omega) (by omega)
      (by omega) (by omega) (by omega)
    rwa [he] at h

/-- The right reflection constraints are literal carried Kunz inequalities. -/
theorem rightBlock_language {m p cap : ℕ} (x : KunzWord m) (hx : x.Valid)
    (hp : 0 < p) (hpm : p < m)
    (hcap : ∀ i, p < i → i < m → KunzWord.coord x i ≤ cap) :
    Language (boundedSystem (KunzWord.coord x p - 1) cap).pairAllowed
      (boundedSystem (KunzWord.coord x p - 1) cap).centerAllowed (rightBlock x p) := by
  apply ofFn_bounded_language
  · intro i
    have hi := i.isLt
    exact ⟨hx.coord_pos (by omega) (by omega), hcap _ (by omega) (by omega)⟩
  · intro i j hij
    have hi := i.isLt
    have hj := j.isLt
    have he : (p + i.val + 1) + (p + j.val + 1) - m = p := by omega
    have h := hx.carry (p + i.val + 1) (p + j.val + 1) (by omega) (by omega)
      (by omega) (by omega) (by omega)
    rw [he] at h
    omega

/-- Splitting at a pivot retains every physical coordinate, in order. -/
theorem list_split_pivot {m p : ℕ} (x : KunzWord m) (hp : 0 < p) (hpm : p < m) :
    List.ofFn x = leftBlock x p ++ KunzWord.coord x p :: rightBlock x p := by
  have hlen : m - 1 = (p - 1) + (m - p - 1 + 1) := by omega
  calc
    List.ofFn x = List.ofFn (fun i : Fin (m - 1) => KunzWord.coord x (i.val + 1)) := by
      congr 1
      funext i
      exact (KunzWord.coord_index x i).symm
    _ = List.ofFn (fun i : Fin ((p - 1) + (m - p - 1 + 1)) =>
          KunzWord.coord x (i.val + 1)) := by
      simpa using List.ofFn_congr hlen (fun i : Fin (m - 1) => KunzWord.coord x (i.val + 1))
    _ = leftBlock x p ++ KunzWord.coord x p :: rightBlock x p := by
      rw [List.ofFn_add, List.ofFn_succ]
      simp only [Fin.val_castLE, Fin.val_natAdd, Fin.val_zero, Nat.add_zero, Fin.val_succ]
      unfold leftBlock rightBlock
      congr 2
      · congr 1
        omega
      · congr 1
        funext i
        congr 1
        omega

/-- Rightmost-maximal choice supplies the cap q−1 on the right block. -/
theorem rightmost_blocks {m : ℕ} (x : KunzWord m) (hx : x.Valid)
    (hdepth : 0 < x.depth) :
    Language (boundedSystem x.depth x.depth).pairAllowed
      (boundedSystem x.depth x.depth).centerAllowed (leftBlock x x.rightmostMaximum) ∧
    Language (boundedSystem (x.depth - 1) (x.depth - 1)).pairAllowed
      (boundedSystem (x.depth - 1) (x.depth - 1)).centerAllowed (rightBlock x x.rightmostMaximum) := by
  have hm := KunzWord.one_lt_multiplicity_of_depth_pos x hdepth
  have hs := KunzWord.rightmostMaximum_spec x hm
  constructor
  · have h := leftBlock_language x hx hs.1 hs.2.1
      (fun i _ _ => KunzWord.coord_le_depth x i)
    simpa only [hs.2.2] using h
  · have h := rightBlock_language (cap := x.depth - 1) x hx hs.1 hs.2.1 (fun i hi him => by
      have := KunzWord.coord_lt_depth_after_rightmost x hi him
      omega)
    simpa only [hs.2.2] using h

/-- The original all-q≥9 relaxation follows from the actual reflected blocks. -/
theorem bounded_to_relaxed_eight {threshold cap : ℕ} (ht : 8 ≤ threshold)
    {w : List ℕ} (h : Language (boundedSystem threshold cap).pairAllowed
      (boundedSystem threshold cap).centerAllowed w) :
    Language OriginalTail.relaxedEightSystem.pairAllowed
      OriginalTail.relaxedEightSystem.centerAllowed w := by
  apply h.mono
  · intro a b hab
    change 1 ≤ a ∧ 1 ≤ b ∧ 8 ≤ a + b
    exact ⟨hab.1, hab.2.2.1, ht.trans hab.2.2.2.2⟩
  · intro a ha
    change 4 ≤ a
    have := ha.2.2
    omega

#print axioms list_split_pivot
#print axioms rightmost_blocks
#print axioms bounded_to_relaxed_eight

end SubmittedGenus.FiniteArithmetic
