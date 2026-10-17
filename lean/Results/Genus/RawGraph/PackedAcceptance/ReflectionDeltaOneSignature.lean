import Results.Genus.RawGraph.PackedAcceptance.ReflectionPairedLetters
import Results.Genus.RawGraph.PackedAcceptance.ReflectionDeltaOneWord

namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord
open SourceModel ReflectionPairedOrbit
open CapFourMass.SignedReflectionPaired

variable {g : ℕ} [NeZero g]

/-- The source signature in the proved canonical paired physical order. -/
def canonicalSignature (n r p δ cap : ℕ) (hp : p=r+g*δ)
    (hc : Nat.Coprime δ (n+2)) (a : Fin g) (ha : a≤mate r a) (ha0 : a≠0)
    (hpair : a≠mate r a) : ComponentSignature cap where
  edges := 2*(n+2)-1
  mask j i := decide (Domain r p cap
    (point n r p δ hp hc a ha ha0 hpair ⟨j.val,by have:=j.isLt; omega⟩).val i.val)
  bound j := edgeBound r p cap
    (point n r p δ hp hc a ha ha0 hpair ⟨j.val,by have:=j.isLt; omega⟩).val
    (point n r p δ hp hc a ha ha0 hpair ⟨j.val+1,by have:=j.isLt; omega⟩).val
  cycle := true
  close := edgeBound r p cap
    (point n r p δ hp hc a ha ha0 hpair ⟨2*(n+2)-1,by omega⟩).val
    (point n r p δ hp hc a ha ha0 hpair 0).val

/-- Closed-form original signature: two ordinary runs and an explicit
terminal carry mask with the actual strong closing edge. -/
def deltaOneSignature (n cap q : ℕ) : ComponentSignature cap where
  edges := 2*(n+2)-1
  mask j := if j.val<2*q then mask cap .fullStrong else mask cap .carryCarry
  bound j := if j.val<2*q then cap else cap-1
  cycle := true
  close := cap

lemma delta_one_mask_formula (n r cap : ℕ) (a : Fin g) (ha0 : a≠0)
    (hp : r+g<g*(n+2)) (k : Fin (n+2)) :
    mask cap (letter (g*(n+2)) r g (a.val+g*k.val))=
      if k.val<cut g a.val r then mask cap .fullStrong else mask cap .carryCarry := by
  have ha : 0<a.val := by have h : a.val≠0 := fun h=>ha0 (Fin.ext h); omega
  rw [delta_one_letter g (n+2) r a.val k.val (NeZero.pos g) ha a.isLt (by omega) hp k.isLt]
  split_ifs <;> rfl

lemma delta_one_even_formula (n r cap : ℕ) (a : Fin g) (ha0 : a≠0)
    (hp : r+g<g*(n+2)) (k : Fin (n+2)) :
    evenBound cap (letter (g*(n+2)) r g (a.val+g*k.val))=
      if k.val<cut g a.val r then cap else cap-1 := by
  have ha : 0<a.val := by have h : a.val≠0 := fun h=>ha0 (Fin.ext h); omega
  rw [delta_one_letter g (n+2) r a.val k.val (NeZero.pos g) ha a.isLt (by omega) hp k.isLt]
  split_ifs <;> simp [evenBound]

lemma delta_one_odd_formula (n r cap : ℕ) (a : Fin g) (ha0 : a≠0)
    (hp : r+g<g*(n+2)) (k : Fin (n+2)) :
    oddBound cap (letter (g*(n+2)) r g (a.val+g*k.val))=
      if k.val<cut g a.val r ∨ k.val=n+1 then cap else cap-1 := by
  have ha : 0<a.val := by have h : a.val≠0 := fun h=>ha0 (Fin.ext h); omega
  have hk:=k.isLt
  rw [delta_one_letter g (n+2) r a.val k.val (NeZero.pos g) ha a.isLt (by omega) hp k.isLt]
  by_cases hq : k.val<cut g a.val r
  · simp [hq,oddBound]
  · by_cases hl : k.val<n+1
    · have hn : k.val≠n+1 := by omega
      simp [hq,hl,hn,oddBound]
    · have he : k.val=n+1 := by omega
      have hq' : ¬n+1<cut g a.val r := by omega
      simp [he,hq',oddBound]

lemma source_mask_delta_one (n r p cap : ℕ) (hr : 0<r)
    (hp : p=r+g*1) (hpm : p<g*(n+2)) (hc : Nat.Coprime 1 (n+2))
    (a : Fin g) (ha : a≤mate r a) (ha0 : a≠0) (hpair : a≠mate r a)
    (j : Fin (2*(n+2))) (i : Fin (cap+1)) :
    decide (Domain r p cap (point n r p 1 hp hc a ha ha0 hpair j).val i.val)=
      (if j.val<2*cut g a.val r then mask cap .fullStrong else mask cap .carryCarry) i := by
  obtain ⟨⟨b,k⟩,rfl⟩ := (parityEquiv (n+2)).symm.surjective j
  have h:=paired_source_letter n r p 1 cap hr (by omega) hp hpm hc a ha ha0 hpair k
  dsimp only at h
  simp only [Nat.one_mul,Nat.mul_one,Nat.mod_eq_of_lt k.isLt] at h
  have hm:=delta_one_mask_formula n r cap a ha0 (by simpa only [hp,Nat.mul_one] using hpm) k
  cases b
  · rw [(h.1 i).1]
    change mask cap _ i=(if 2*k.val<2*cut g a.val r then mask cap .fullStrong else mask cap .carryCarry) i
    rw [hm]
    simp only [show 2*k.val<2*cut g a.val r ↔ k.val<cut g a.val r by omega]
  · rw [(h.1 i).2]
    change mask cap _ i=(if 2*k.val+1<2*cut g a.val r then mask cap .fullStrong else mask cap .carryCarry) i
    rw [hm]
    simp only [show 2*k.val+1<2*cut g a.val r ↔ k.val<cut g a.val r by omega]

lemma source_edge_delta_one (n r p cap : ℕ) (hr : 0<r)
    (hp : p=r+g*1) (hpm : p<g*(n+2)) (hc : Nat.Coprime 1 (n+2))
    (a : Fin g) (ha : a≤mate r a) (ha0 : a≠0) (hpair : a≠mate r a)
    (j : Fin (2*(n+2)-1)) :
    edgeBound r p cap
      (point n r p 1 hp hc a ha ha0 hpair ⟨j.val,by have:=j.isLt; omega⟩).val
      (point n r p 1 hp hc a ha ha0 hpair ⟨j.val+1,by have:=j.isLt; omega⟩).val=
      if j.val<2*cut g a.val r then cap else cap-1 := by
  let k : Fin (n+2) := ⟨j.val/2,by have:=j.isLt; omega⟩
  have hk : k.val<n+2 := k.isLt
  have h:=paired_source_letter n r p 1 cap hr (by omega) hp hpm hc a ha ha0 hpair k
  dsimp only at h
  simp only [Nat.one_mul,Nat.mul_one,Nat.mod_eq_of_lt k.isLt] at h
  have hp' : r+g<g*(n+2) := by simpa only [hp,Nat.mul_one] using hpm
  by_cases he : j.val%2=0
  · have hj : j.val=2*k.val := by dsimp [k]; omega
    have e1 : (⟨j.val,by have:=j.isLt; omega⟩:Fin (2*(n+2)))=(parityEquiv (n+2)).symm (false,k) := Fin.ext hj
    have e2 : (⟨j.val+1,by have:=j.isLt; omega⟩:Fin (2*(n+2)))=(parityEquiv (n+2)).symm (true,k) := Fin.ext (by simpa only [hj,parityEquiv_symm_odd])
    rw [e1,e2,h.2.1,delta_one_even_formula n r cap a ha0 hp' k]
    simp only [show j.val<2*cut g a.val r ↔ k.val<cut g a.val r by omega]
  · have hj : j.val=2*k.val+1 := by dsimp [k]; omega
    have hkl : k.val+1<n+2 := by have:=j.isLt; omega
    have e1 : (⟨j.val,by have:=j.isLt; omega⟩:Fin (2*(n+2)))=(parityEquiv (n+2)).symm (true,k) := Fin.ext hj
    have e2 : (⟨j.val+1,by have:=j.isLt; omega⟩:Fin (2*(n+2)))=(parityEquiv (n+2)).symm (false,next k) := by
      apply Fin.ext
      change j.val+1=2*((k.val+1)%(n+2))
      rw [Nat.mod_eq_of_lt hkl]
      omega
    rw [e1,e2,h.2.2,delta_one_odd_formula n r cap a ha0 hp' k]
    simp only [show k.val≠n+1 by omega,or_false,
      show j.val<2*cut g a.val r ↔ k.val<cut g a.val r by omega]

lemma source_close_delta_one (n r p cap : ℕ) (hr : 0<r)
    (hp : p=r+g*1) (hpm : p<g*(n+2)) (hc : Nat.Coprime 1 (n+2))
    (a : Fin g) (ha : a≤mate r a) (ha0 : a≠0) (hpair : a≠mate r a) :
    edgeBound r p cap
      (point n r p 1 hp hc a ha ha0 hpair ⟨2*(n+2)-1,by omega⟩).val
      (point n r p 1 hp hc a ha ha0 hpair 0).val=cap := by
  let k : Fin (n+2) := ⟨n+1,by omega⟩
  have h:=paired_source_letter n r p 1 cap hr (by omega) hp hpm hc a ha ha0 hpair k
  dsimp only at h
  simp only [Nat.one_mul,Nat.mul_one,Nat.mod_eq_of_lt k.isLt] at h
  have hp' : r+g<g*(n+2) := by simpa only [hp,Nat.mul_one] using hpm
  have e1 : (⟨2*(n+2)-1,by omega⟩:Fin (2*(n+2)))=(parityEquiv (n+2)).symm (true,k) := by
    apply Fin.ext
    change 2*(n+2)-1=2*(n+1)+1
    omega
  have e2 : (0:Fin (2*(n+2)))=(parityEquiv (n+2)).symm (false,next k) := by
    apply Fin.ext
    change 0=2*(((n+1)+1)%(n+2))
    simp [Nat.add_assoc]
  rw [e1,e2,h.2.2,delta_one_odd_formula n r cap a ha0 hp' k]
  simp [k]

/-- Uniform original-source signature identity, discharged by arithmetic,
with no expanded per-vertex mask/threshold checker. -/
theorem canonicalSignature_delta_one (n r p cap : ℕ) (hr : 0<r)
    (hp : p=r+g*1) (hpm : p<g*(n+2)) (hc : Nat.Coprime 1 (n+2))
    (a : Fin g) (ha : a≤mate r a) (ha0 : a≠0) (hpair : a≠mate r a) :
    canonicalSignature n r p 1 cap hp hc a ha ha0 hpair=
      deltaOneSignature n cap (cut g a.val r) := by
  unfold canonicalSignature deltaOneSignature
  congr 1
  · funext j i
    exact source_mask_delta_one n r p cap hr hp hpm hc a ha ha0 hpair _ i
  · funext j
    exact source_edge_delta_one n r p cap hr hp hpm hc a ha ha0 hpair j
  · exact source_close_delta_one n r p cap hr hp hpm hc a ha ha0 hpair

#print axioms canonicalSignature_delta_one
end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord
