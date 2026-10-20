import Results.Genus.CapFourMass.GadgetLocalSums
import Results.Genus.CapFourMass.CompletionSurvival

namespace SubmittedGenus.CapFourMass.GadgetFibers
open scoped BigOperators
open ContractionGeometry RawGraph GadgetCoordinates
noncomputable section
attribute [local instance] Classical.propDecidable

abbrev Outside (m r p i : ℕ) := {v : Fin (m-1) // physical v ∉ Gadget m r p i} → Fin 5

def reindex {m r p i n : ℕ} (e : Fin n ≃ PhysicalVertices m r p i) :
    (PhysicalVertices m r p i → Fin 5) ≃ (Fin n → Fin 5) where
  toFun g k := g (e k)
  invFun a v := a (e.symm v)
  left_inv g := by funext v; simp
  right_inv a := by funext k; simp

def word {m r p i n : ℕ} (e : Fin n ≃ PhysicalVertices m r p i)
    (a : Fin n → Fin 5) (b : Outside m r p i) : Fin (m-1) → Fin 5 :=
  CoordinateFibers.join (fun v => physical v ∈ Gadget m r p i) ((reindex e).symm a) b

def naturalWord {m r p i n : ℕ} (e : Fin n ≃ PhysicalVertices m r p i)
    (a : Fin n → Fin 5) (b : Outside m r p i) : Word m := boundedWord (word e a b)

@[simp] lemma word_inside {m r p i n : ℕ} (e : Fin n ≃ PhysicalVertices m r p i)
    (a : Fin n → Fin 5) (b : Outside m r p i) (k : Fin n) :
    word e a b (e k).val = a k := by
  rw [word,CoordinateFibers.join_inside (fun v : Fin (m-1) => physical v ∈ Gadget m r p i) ((reindex e).symm a) b (e k).val (e k).property]
  change a (e.symm (e k)) = a k
  simp

@[simp] lemma word_outside {m r p i n : ℕ} (e : Fin n ≃ PhysicalVertices m r p i)
    (a : Fin n → Fin 5) (b : Outside m r p i) (v : Fin (m-1))
    (hv : physical v ∉ Gadget m r p i) : word e a b v = b ⟨v,hv⟩ := by
  exact CoordinateFibers.join_outside _ _ _ v hv

lemma same_exterior {m r p i n : ℕ} (e : Fin n ≃ PhysicalVertices m r p i)
    (a a' : Fin n → Fin 5) (b : Outside m r p i) (v : Fin (m-1))
    (hv : physical v ∉ Gadget m r p i) : naturalWord e a b v = naturalWord e a' b v := by
  simp only [naturalWord,boundedWord,word_outside e a b v hv,word_outside e a' b v hv]

@[simp] lemma natural_inside {m r p i n : ℕ} (e : Fin n ≃ PhysicalVertices m r p i)
    (a : Fin n → Fin 5) (b : Outside m r p i) (k : Fin n) :
    naturalWord e a b (e k).val = (a k).val := by
  simp [naturalWord,boundedWord]

@[simp] lemma coord_inside {m r p i n : ℕ} (e : Fin n ≃ PhysicalVertices m r p i)
    (a : Fin n → Fin 5) (b : Outside m r p i) (k : Fin n) :
    KunzWord.coord (naturalWord e a b) (physical (e k).val) = (a k).val := by
  simp only [physical,KunzWord.coord_index,natural_inside]

lemma inner_weight {m r p i n : ℕ} (e : Fin n ≃ PhysicalVertices m r p i)
    (a : Fin n → Fin 5) (z : ℝ) :
    (∏ v : PhysicalVertices m r p i, z^(((reindex e).symm a) v).val) =
      GadgetLocalSums.weight z a := by
  symm
  apply Fintype.prod_equiv e
  intro k
  simp [reindex,GadgetLocalSums.letter]

lemma partition_split {m r p i n : ℕ} (e : Fin n ≃ PhysicalVertices m r p i)
    (z : ℝ) (P : (Fin (m-1) → Fin 5) → Prop) :
    (∑ x, if P x then ∏ v, z^(x v).val else 0) =
    ∑ b : Outside m r p i, (∏ v, z^(b v).val) *
      (∑ a : Fin n → Fin 5, if P (word e a b) then GadgetLocalSums.weight z a else 0) := by
  classical
  rw [CoordinateFibers.partition_split (fun v => physical v ∈ Gadget m r p i)
    (fun (_ : Fin (m-1)) (a : Fin 5) => z^a.val) P]
  apply Finset.sum_congr rfl
  intro b hb
  congr 1
  apply Fintype.sum_equiv (reindex e)
  intro g
  have hg : (reindex e).symm ((reindex e) g) = g := (reindex e).symm_apply_apply g
  have hw := inner_weight e ((reindex e) g) z
  rw [hg] at hw
  have hj : word e ((reindex e) g) b =
      CoordinateFibers.join (fun v => physical v ∈ Gadget m r p i) g b := by
    unfold word
    rw [hg]
  rw [hj]
  split_ifs
  · exact hw
  · rfl

end
end SubmittedGenus.CapFourMass.GadgetFibers
