import Results.Genus.RawGraph.PackedAcceptance.ReflectionBitProgram

namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord

lemma euclidean_remainder_half (L d : ℕ) (hd : 0<d) (hdL : d<L) : L%d≤L/2 := by
  by_cases h : 2*d≤L
  · have hr:=Nat.mod_lt L hd
    omega
  · rw [Nat.mod_eq_sub_mod hdL.le,Nat.mod_eq_of_lt (by omega : L-d<d)]
    omega

lemma log2_mono_bound (a b : ℕ) (hab : a≤b) : a.log2≤b.log2 := by
  by_cases ha : a=0
  · subst a
    simp
  · exact (Nat.le_log2 (by omega : b≠0)).mpr ((Nat.log2_self_le ha).trans hab)

/-- Every two positive-remainder stages halve the modulus. This excludes
the linear predecessor behavior of naive negative-step recursion. -/
theorem bitCompile_depth_bound (L d q : ℕ) (tail rev : Bool) :
    (bitCompile L d q tail rev).depth≤2*L.log2+1 := by
  rw [bitCompile]
  split
  · rename_i h
    simp only [BitProgram.depth]
    by_cases hr : 0<L%d
    · rw [bitCompile,dif_pos ⟨hr,Nat.mod_lt L h.1⟩]
      simp only [BitProgram.depth]
      have ih:=bitCompile_depth_bound (L%d) (d%(L%d)) ((q%d)%(L%d)) true (!(!rev))
      have hm:=log2_mono_bound (L%d) (L/2) (euclidean_remainder_half L d h.1 h.2)
      have he : L.log2=(L/2).log2+1 := by
        rw [Nat.log2_def,if_pos (by omega : 2≤L)]
      omega
    · have hz : L%d=0 := by omega
      rw [bitCompile,dif_neg (by simp [hz])]
      simp [BitProgram.depth]
  · simp [BitProgram.depth]
termination_by L
decreasing_by
  simp_wf
  exact lt_trans (Nat.mod_lt L (by omega : 0<d)) (by omega)

theorem bitCompile_size_logarithmic (L d q : ℕ) (tail rev : Bool) :
    (bitCompile L d q tail rev).size≤72*L.log2+38 := by
  have hs:=bitCompile_size L d q tail rev
  have hd:=bitCompile_depth_bound L d q tail rev
  omega

#print axioms bitCompile_depth_bound
#print axioms bitCompile_size_logarithmic
end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord
