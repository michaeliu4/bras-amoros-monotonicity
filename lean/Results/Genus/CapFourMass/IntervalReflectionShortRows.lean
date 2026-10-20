import Results.Genus.CapFourMass.IntervalIndexedShortRows
import Results.Genus.CapFourMass.IntervalSignatureTables
import Results.Genus.RawGraph.SignatureCheck
import Results.Genus.RawGraph.PackedAcceptance.ReflectionOriginalLayout

/-! Compact original short-row certificates. The generic reflected layout
already covers the actual source, so a row supplies only signature keys.
Fieldwise matching retains all masks, ordered edges and closing states. -/
namespace SubmittedGenus.CapFourMass.Interval.ReflectionShortRows
open RawGraph RawGraph.LayoutCompiler RawGraph.PackedAcceptance

lemma pivot_lt {p : ℕ} (r : Fin (p-1)) : r.val+1<p := by omega

abbrev layout {p : ℕ} (r : Fin (p-1)) (j : Fin p) : Layout (p+1+j.val) :=
  ReflectionOriginalLayout.layout (p+1+j.val) (r.val+1) p (pivot_lt r) (by omega)

def graphKeys {p : ℕ} (keys : Array (Array ℕ)) (r : Fin (p-1)) (j : Fin p) : Array ℕ :=
  keys[r.val*p+j.val]?.getD #[]

def rawKey {p : ℕ} (keys : Array (Array ℕ)) (r : Fin (p-1)) (j : Fin p)
    (c : Fin (layout r j).count) : ℕ := (graphKeys keys r j)[c.val]?.getD 0

def key {p k : ℕ} (hk : 0<k) (keys : Array (Array ℕ))
    (r : Fin (p-1)) (j : Fin p) (c : Fin (layout r j).count) : Fin k :=
  ⟨rawKey keys r j c % k, Nat.mod_lt _ hk⟩

def KeysValid {p k : ℕ} (keys : Array (Array ℕ)) : Prop :=
  keys.size=(p-1)*p ∧ ∀ (r : Fin (p-1)) (j : Fin p),
    (graphKeys keys r j).size=(layout r j).count ∧
    ∀ c : Fin (layout r j).count, rawKey keys r j c<k

instance {p k : ℕ} (keys : Array (Array ℕ)) : Decidable (KeysValid (p:=p) (k:=k) keys) := by
  unfold KeysValid
  infer_instance

def Matches {p k : ℕ} (hk : 0<k) (cache : Fin k→ComponentSignature 4)
    (keys : Array (Array ℕ)) : Prop :=
  ∀ (r : Fin (p-1)) (j : Fin p) (c : Fin (layout r j).count),
    SameSignature (physicalSignature (layout r j) (r.val+1) p 4 c)
      (cache (key hk keys r j c))

instance {p k : ℕ} (hk : 0<k) (cache : Fin k→ComponentSignature 4)
    (keys : Array (Array ℕ)) : Decidable (Matches (p:=p) hk cache keys) := by
  unfold Matches
  infer_instance

def graphBox {p k : ℕ} (hk : 0<k) (boxes : Fin k→Box)
    (keys : Array (Array ℕ)) (r : Fin (p-1)) (j : Fin p) : Box :=
  prodBoxes (fun c=>boxes (key hk keys r j c))

theorem graph_contains {p k : ℕ} (hk : 0<k) (cache : Fin k→ComponentSignature 4)
    (boxes : Fin k→Box) (keys : Array (Array ℕ))
    (hs : Matches (p:=p) hk cache keys)
    (hb : ∀ i, Contains (boxes i) (signatureScalar (cache i) radius))
    (r : Fin (p-1)) (j : Fin p) :
    Contains (graphBox hk boxes keys r j)
      (Polynomial.eval₂ (Nat.castRingHom ℝ) radius (rawPolynomial (p+1+j.val) (r.val+1) p 4)) := by
  apply SignatureTables.cache_layout_contains (layout r j)
  · unfold Parameters
    have hr := pivot_lt r
    omega
  · exact ReflectionOriginalLayout.covers _ _ _ _ (pivot_lt r) (by omega)
  · exact fun c=>sameSignature_sound (hs r j c)
  · exact hb

def rowBox {p k : ℕ} (hk : 0<k) (boxes : Fin k→Box) (keys : Array (Array ℕ)) : Box :=
  IndexedShort.rowBox (fun r : Fin (p-1)=>IndexedShort.pairBox (graphBox hk boxes keys r))

theorem row_contains {p k : ℕ} (hk : 0<k) (cache : Fin k→ComponentSignature 4)
    (boxes : Fin k→Box) (keys : Array (Array ℕ))
    (hs : Matches (p:=p) hk cache keys)
    (hb : ∀ i, Contains (boxes i) (signatureScalar (cache i) radius)) :
    Contains (rowBox (p:=p) hk boxes keys) (originalShortRow p) := by
  apply IndexedShort.row_contains
  intro r
  apply IndexedShort.pair_contains
  exact graph_contains hk cache boxes keys hs hb r

end SubmittedGenus.CapFourMass.Interval.ReflectionShortRows
