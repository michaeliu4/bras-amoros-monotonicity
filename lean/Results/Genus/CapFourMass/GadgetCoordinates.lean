import Results.Genus.CapFourMass.LocalPartitions

namespace SubmittedGenus.CapFourMass.GadgetCoordinates
open ContractionGeometry RawGraph
noncomputable section

abbrev Vertices (m r p i : ℕ) := {j : ℕ // j ∈ Gadget m r p i}
abbrev PhysicalVertices (m r p i : ℕ) :=
  {v : Fin (m-1) // physical v ∈ Gadget m r p i}

lemma member_bounds {m r p i j : ℕ} (hr : 1 ≤ r) (hrp : r < p)
    (hi : Eligible m p i) (hj : j ∈ Gadget m r p i) : 0 < j ∧ j < m := by
  have hg := gadget_bounds hr hrp hi
  simp only [Gadget, Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with rfl | rfl | rfl | rfl <;> omega

/-- Every gadget label denotes exactly one genuine physical word coordinate. -/
def physicalEquiv {m r p i : ℕ} (hr : 1 ≤ r) (hrp : r < p)
    (hi : Eligible m p i) : PhysicalVertices m r p i ≃ Vertices m r p i where
  toFun v := ⟨physical v.val,v.property⟩
  invFun j :=
    let hb := member_bounds hr hrp hi j.property
    ⟨⟨j.val-1,by omega⟩, by simpa only [physical,Nat.sub_add_cancel hb.1] using j.property⟩
  left_inv v := by
    apply Subtype.ext
    apply Fin.ext
    simp [physical]
  right_inv j := by
    apply Subtype.ext
    have hb := member_bounds hr hrp hi j.property
    simp [physical,Nat.sub_add_cancel hb.1]

def label3 (m r p i : ℕ) : Fin 3 → Vertices m r p i :=
  ![⟨i,by simp [Gadget]⟩,⟨m+r-i,by simp [Gadget]⟩,⟨m+p-i,by simp [Gadget]⟩]

def label4 (m r p i : ℕ) : Fin 4 → Vertices m r p i :=
  ![⟨i,by simp [Gadget]⟩,⟨2*i,by simp [Gadget]⟩,
    ⟨m+r-i,by simp [Gadget]⟩,⟨m+p-i,by simp [Gadget]⟩]

theorem label3_bijective {m r p i : ℕ} (hr : 1 ≤ r) (hrp : r < p)
    (hi : Eligible m p i) (hshared : 2*i=m+r-i ∨ 2*i=m+p-i) :
    Function.Bijective (label3 m r p i) := by
  have hdist := only_target_leaf_identifications hr hrp hi
  constructor
  · intro u v he
    have he' := congrArg Subtype.val he
    fin_cases u <;> fin_cases v <;> simp [label3] at he' ⊢ <;> omega
  · rintro ⟨j,hj⟩
    simp only [Gadget, Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl | rfl
    · exact ⟨0,rfl⟩
    · rcases hshared with h | h
      · refine ⟨1,Subtype.ext ?_⟩
        simpa [label3] using h.symm
      · refine ⟨2,Subtype.ext ?_⟩
        simpa [label3] using h.symm
    · exact ⟨1,rfl⟩
    · exact ⟨2,rfl⟩

theorem label4_bijective {m r p i : ℕ} (hr : 1 ≤ r) (hrp : r < p)
    (hi : Eligible m p i) (hnr : 2*i ≠ m+r-i) (hnp : 2*i ≠ m+p-i) :
    Function.Bijective (label4 m r p i) := by
  have hdist := only_target_leaf_identifications hr hrp hi
  constructor
  · intro u v he
    have he' := congrArg Subtype.val he
    fin_cases u <;> fin_cases v <;> simp [label4] at he' ⊢ <;> omega
  · rintro ⟨j,hj⟩
    simp only [Gadget, Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl | rfl
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨2,rfl⟩
    · exact ⟨3,rfl⟩

/-- The three-state geometry covers either target-leaf identification. -/
def equiv3 {m r p i : ℕ} (hr : 1 ≤ r) (hrp : r < p)
    (hi : Eligible m p i) (hshared : 2*i=m+r-i ∨ 2*i=m+p-i) :
    Fin 3 ≃ PhysicalVertices m r p i :=
  (Equiv.ofBijective _ (label3_bijective hr hrp hi hshared)).trans
    (physicalEquiv hr hrp hi).symm

/-- The four distinct physical coordinates, in center/target/leaf order. -/
def equiv4 {m r p i : ℕ} (hr : 1 ≤ r) (hrp : r < p)
    (hi : Eligible m p i) (hnr : 2*i ≠ m+r-i) (hnp : 2*i ≠ m+p-i) :
    Fin 4 ≃ PhysicalVertices m r p i :=
  (Equiv.ofBijective _ (label4_bijective hr hrp hi hnr hnp)).trans
    (physicalEquiv hr hrp hi).symm

@[simp] theorem physical_inverse {m r p i : ℕ} (hr : 1 ≤ r) (hrp : r < p)
    (hi : Eligible m p i) (j : Vertices m r p i) :
    physical ((physicalEquiv hr hrp hi).symm j).val = j.val :=
  congrArg Subtype.val ((physicalEquiv hr hrp hi).apply_symm_apply j)

@[simp] theorem equiv3_physical {m r p i : ℕ} (hr : 1 ≤ r) (hrp : r < p)
    (hi : Eligible m p i) (hshared : 2*i=m+r-i ∨ 2*i=m+p-i) (k : Fin 3) :
    physical ((equiv3 hr hrp hi hshared) k).val = (label3 m r p i k).val := by
  exact physical_inverse hr hrp hi _

@[simp] theorem equiv4_physical {m r p i : ℕ} (hr : 1 ≤ r) (hrp : r < p)
    (hi : Eligible m p i) (hnr : 2*i ≠ m+r-i) (hnp : 2*i ≠ m+p-i) (k : Fin 4) :
    physical ((equiv4 hr hrp hi hnr hnp) k).val = (label4 m r p i k).val := by
  exact physical_inverse hr hrp hi _

end
end SubmittedGenus.CapFourMass.GadgetCoordinates
