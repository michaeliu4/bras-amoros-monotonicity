import Results.Genus.FixedPivot.ConditionedTransfer
import Results.Genus.FixedPivot.CoreSource

/-! The exact original cap-four source in canonical carry parameters. -/
namespace SubmittedGenus.FixedPivot
open RawGraph RawGraph.SourceModel RawGraph.Conditioning
open scoped BigOperators
noncomputable section

/-- The physical carry port r+a+1 is core index r+a. -/
def canonicalPortIndex (r d : ℕ) (a : Fin d) : Fin (r+d) :=
  ⟨r+a.val, by have := a.isLt; omega⟩

def canonicalPortAllowed {r d : ℕ} (x : Fin (r+d)→Fin 5) (a : Fin d) (v : ℕ) : Prop :=
  a.val+1=d ∨ 3≤(x (canonicalPortIndex r d a)).val+v

instance {r d : ℕ} (x : Fin (r+d)→Fin 5) (a : Fin d) (v : ℕ) :
    Decidable (canonicalPortAllowed x a v) := by
  unfold canonicalPortAllowed; infer_instance

def canonicalStartAllowed {r N d : ℕ} {hN : d<N}
    (x : Fin (r+d)→Fin 5) (c : CarryRepresentative N d hN) (v : Fin 3) : Prop :=
  canonicalPortAllowed x c.val (v.val+1)

def canonicalFinishAllowed {r N d : ℕ} {hN : d<N}
    (x : Fin (r+d)→Fin 5) (c : CarryRepresentative N d hN) (v : Fin 3) : Prop :=
  if c.val=portPartner N d hN c.val then 2≤v.val+1
  else canonicalPortAllowed x (portPartner N d hN c.val) (v.val+1)

instance {r N d : ℕ} {hN : d<N} (x : Fin (r+d)→Fin 5)
    (c : CarryRepresentative N d hN) : DecidablePred (canonicalStartAllowed x c) := by
  intro v; unfold canonicalStartAllowed; infer_instance
instance {r N d : ℕ} {hN : d<N} (x : Fin (r+d)→Fin 5)
    (c : CarryRepresentative N d hN) : DecidablePred (canonicalFinishAllowed x c) := by
  intro v; unfold canonicalFinishAllowed; infer_instance

lemma canonicalParameters {r N d : ℕ} (hr : 0<r) (hd : 0<d) (hN : d<N) :
    Parameters (r+N) r (r+d) 4 := by
  exact ⟨hr, by omega, by omega, by decide⟩

/-- Transport the source contraction before specializing the canonical parameters.
The auxiliary core size p permits dependent carry indices to be eliminated
by equality induction, rather than by an unverified indexing convention. -/
private def portIndexAt (r p d : ℕ) (hrd : r+d≤p) (a : Fin d) : Fin p :=
  ⟨r+a.val,by have := a.isLt; omega⟩

private theorem source_transport {m r p N d : ℕ} (hp : Parameters m r p 4)
    (hm : 2*p<m) (hN : d<N) (hn : m-r=N) (hd : p-r=d) (hrd : r+d≤p)
    {R : Type*} [CommRing R] (z : R) :
    Polynomial.eval₂ (Nat.castRingHom R) z (rawPolynomial m r p 4)=
      ∑ x : Fin p→Fin 5,
        Polynomial.eval₂ (Nat.castRingHom R) z (stableCoreTerm r p x)*
        ∏ c : CarryRepresentative N d hN,
          weightedCarryKernel z (carryTailSize N d hN c-1)
            (fun v => if c.val.val+1=d ∨ 3≤(x (portIndexAt r p d hrd c.val)).val+(v.val+1) then 1 else 0)
            (fun v => if (if c.val=portPartner N d hN c.val then 2≤v.val+1
              else (portPartner N d hN c.val).val+1=d ∨
                3≤(x (portIndexAt r p d hrd (portPartner N d hN c.val))).val+(v.val+1)) then 1 else 0) := by
  subst N
  subst d
  have hh := rawPolynomial_eval_eq_core_kernels hp hm z
  simp_rw [conditioning_core_term] at hh
  have hf : instFintypeTailRepresentative hp =
      (Subtype.fintype (fun a : Fin (p-r) => portPartner (m-r) (p-r) hN a ≤ a)) := Subsingleton.elim _ _
  rw [hf] at hh
  simp only [TailRepresentative,conditionedTailEdges,sourceStartAllowed,sourceFinishAllowed,
    sourcePortAllowed,conditionedPortIndex] at hh
  rw [hh]
  apply Finset.sum_congr rfl
  intro x _
  congr 1


/-- No multiplicity-dependent core or subtraction-indexed port survives: this
is the source-exact canonical finite contraction used in the phase argument. -/
theorem rawPolynomial_eval_eq_canonical_kernels {r N d : ℕ}
    (hr : 0<r) (hd : 0<d) (hN : d<N) (hbig : r+2*d<N)
    {R : Type*} [CommRing R] (z : R) :
    Polynomial.eval₂ (Nat.castRingHom R) z (rawPolynomial (r+N) r (r+d) 4)=
      ∑ x : Fin (r+d)→Fin 5,
        Polynomial.eval₂ (Nat.castRingHom R) z (stableCoreTerm r (r+d) x)*
        ∏ c : CarryRepresentative N d hN,
          weightedCarryKernel z (carryTailSize N d hN c-1)
            (fun v => if canonicalStartAllowed x c v then 1 else 0)
            (fun v => if canonicalFinishAllowed x c v then 1 else 0) := by
  have hp := canonicalParameters hr hd hN
  have hm : 2*(r+d)<r+N := by omega
  have hh := source_transport hp hm hN (by omega) (by omega) (by omega) z
  rw [hh]
  apply Finset.sum_congr rfl
  intro x _
  congr 1


end
end SubmittedGenus.FixedPivot
