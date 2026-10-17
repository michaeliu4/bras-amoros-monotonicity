import Results.Genus.RawGraph.PackedAcceptance.ReflectionOrbitOrientation

/-! Quotient-block extraction for an arbitrary ordered interval alphabet.
This is the composable interface needed when transformed cuts no longer
include the new wrap boundary. It does not sort or guess those cuts. -/
namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord

/-- The ordered symbols in an affine progression through a finite interval
partition. The boundaries may include zero-length intervals. -/
theorem affine_interval_word {A : Type*} (F c : ℕ→A) (b : ℕ→ℕ)
    (K δ s : ℕ) (hδ : 0<δ) (hb : Monotone b) (hzero : b 0=0)
    (hF : ∀j, j<K → ∀t, b j≤t → t<b (j+1) → F t=c j) :
    (List.range (cut δ s (b K))).map (fun i=>F (s+δ*i))=
      (List.range K).flatMap (fun j=>
        List.replicate (cut δ s (b (j+1))-cut δ s (b j)) (c j)) := by
  let d : ℕ→ℕ := fun j=>cut δ s (b j)
  have hd : Monotone d := (cut_mono δ s hδ).comp hb
  have hd0 : d 0=0 := by simp [d,hzero,cut]
  have hi:=ranges_at_boundaries d hd K
  rw [hd0,Nat.sub_zero,←List.range_eq_range'] at hi
  change (List.range (d K)).map (fun i=>F (s+δ*i))=_
  rw [←hi,List.map_flatMap]
  apply List.flatMap_congr
  intro j hj
  have hjK : j<K := List.mem_range.mp hj
  rw [List.range'_eq_map_range,List.map_map]
  have hmap : (List.range (d (j+1)-d j)).map
      (fun i=>F (s+δ*(d j+i)))=(List.range (d (j+1)-d j)).map (fun _=>c j) := by
    apply List.map_congr_left
    intro i hi
    have hil : i<d (j+1)-d j := List.mem_range.mp hi
    have hmono : d j≤d (j+1) := hd (Nat.le_succ j)
    have hlow : d j≤d j+i := by omega
    have hhigh : d j+i<d (j+1) := by omega
    apply hF j hjK
    · exact (cut_le_iff δ s (b j) (d j+i) hδ).mp hlow
    · exact (lt_cut_iff δ s (b (j+1)) (d j+i) hδ).mp hhigh
  change (List.range (d (j+1)-d j)).map (fun i=>F (s+δ*(d j+i)))=_
  rw [hmap]
  simp [d]

/-- One complete quotient chunk for an arbitrary interval alphabet. -/
theorem modular_interval_chunk {A : Type*} (F c : ℕ→A) (b : ℕ→ℕ)
    (K L δ j : ℕ) (hδ : 0<δ) (hb : Monotone b) (hzero : b 0=0) (hend : b K=L)
    (hF : ∀h, h<K → ∀t, b h≤t → t<b (h+1) → F t=c h) :
    (List.range' (chunkBoundary L δ j) (chunkLength L δ j)).map (fun k=>F ((δ*k)%L))=
      (List.range K).flatMap (fun h=>
        List.replicate
          (cut δ (chunkStart L δ j) (b (h+1))-cut δ (chunkStart L δ j) (b h)) (c h)) := by
  have hh:=affine_interval_word F c b K δ (chunkStart L δ j) hδ hb hzero hF
  rw [hend,←chunkLength_eq_cut L δ j hδ] at hh
  rw [←hh,List.range'_eq_map_range,List.map_map]
  apply List.map_congr_left
  intro i hi
  dsimp only [Function.comp_def]
  rw [chunk_coordinate L δ j i hδ (List.mem_range.mp hi)]

/-- A closed-form macro at an arbitrary phase below delta. This definition
contains only ordered powers of the existing interval symbols. -/
def intervalMacro {A : Type*} (c : ℕ→A) (b : ℕ→ℕ) (K δ s : ℕ) : List A :=
  (List.range K).flatMap (fun h=>List.replicate
    ((b (h+1)/δ+(if s<b (h+1)%δ then 1 else 0))-
      (b h/δ+(if s<b h%δ then 1 else 0))) (c h))

lemma intervalMacro_eq_cuts {A : Type*} (c : ℕ→A) (b : ℕ→ℕ) (K δ s : ℕ)
    (hδ : 0<δ) (hs : s<δ) :
    intervalMacro c b K δ s=(List.range K).flatMap (fun h=>List.replicate
      (cut δ s (b (h+1))-cut δ s (b h)) (c h)) := by
  unfold intervalMacro
  apply List.flatMap_congr
  intro h _
  rw [cut_residue_formula δ s (b (h+1)) hδ hs,cut_residue_formula δ s (b h) hδ hs]

/-- General exact reduction to negative-phase interval macros; no special
ordering between the transformed cuts is assumed. -/
theorem modular_interval_macros {A : Type*} (F c : ℕ→A) (b : ℕ→ℕ)
    (K L δ : ℕ) (hδ : 0<δ) (hb : Monotone b) (hzero : b 0=0) (hend : b K=L)
    (hF : ∀h, h<K → ∀t, b h≤t → t<b (h+1) → F t=c h) :
    (List.range L).map (fun k=>F ((δ*k)%L))=
      (List.range δ).flatMap (fun j=>intervalMacro c b K δ (-((j*L:ℕ):ZMod δ)).val) := by
  conv_lhs => rw [←original_index_chunks L δ hδ]
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro j _
  rw [modular_interval_chunk F c b K L δ j hδ hb hzero hend hF,
    ←chunkStart_negative_mod L δ j hδ,
    intervalMacro_eq_cuts c b K δ (chunkStart L δ j) hδ (chunkStart_spec L δ j hδ).1]

/-- A composable positive Euclidean remainder interface for arbitrary
interval alphabets. Reverse macro order before substituting its symbols. -/
theorem modular_interval_positive_remainder {A : Type*} (F c : ℕ→A) (b : ℕ→ℕ)
    (K L δ : ℕ) (hδ : 0<δ) (hb : Monotone b) (hzero : b 0=0) (hend : b K=L)
    (hF : ∀h, h<K → ∀t, b h≤t → t<b (h+1) → F t=c h) :
    (List.range L).map (fun k=>F ((δ*k)%L))=
      intervalMacro c b K δ 0 ++
        (((List.range' 1 (δ-1)).map (fun j=>intervalMacro c b K δ (((L%δ)*j)%δ))).reverse).flatten := by
  rw [modular_interval_macros F c b K L δ hδ hb hzero hend hF,List.flatMap_def]
  have hh:=negative_orbit_word_pos (intervalMacro c b K δ) δ L hδ
  simp only [Nat.mul_comm L] at hh
  rw [hh,List.flatten_cons]

#print axioms affine_interval_word
#print axioms modular_interval_macros
#print axioms modular_interval_positive_remainder
end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord
