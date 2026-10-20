import Results.Genus.RawGraph.PackedAcceptance.SourceBound

namespace SubmittedGenus.RawGraph.PackedAcceptance
open Packing

/-- Discarding a polynomial's high coefficients preserves its packed residue.
No bound on the discarded coefficients is needed. -/
lemma eval_mod_eq_prefix (p : Polynomial ℕ) (base cutoff : ℕ) :
    p.eval base % base^cutoff =
      pack base (fun i:Fin cutoff => p.coeff i.val) % base^cutoff := by
  let n := p.natDegree+cutoff+1
  have hn : p.natDegree<n := by dsimp [n]; omega
  have hc : cutoff≤n := by dsimp [n]; omega
  rw [eval_eq_pack p hn]
  unfold pack
  have ht : (List.ofFn (fun i:Fin n => p.coeff i.val)).take cutoff =
      List.ofFn (fun i:Fin cutoff => p.coeff i.val) := by
    apply List.ext_getElem
    · simp only [List.length_take,List.length_ofFn,Nat.min_eq_left hc]
    · intro i hi hj
      simp only [List.getElem_take,List.getElem_ofFn]
  have he := Nat.ofDigits_append (b := base)
    (l1 := (List.ofFn (fun i:Fin n => p.coeff i.val)).take cutoff)
    (l2 := (List.ofFn (fun i:Fin n => p.coeff i.val)).drop cutoff)
  rw [List.take_append_drop,ht,List.length_ofFn] at he
  rw [he,Nat.add_mul_mod_self_left]

/-- Source coefficient extraction needs a no-carry bound only below the
cutoff, exactly as required for the submitted truncated computation. -/
theorem digit_eval_of_prefix_bound (p : Polynomial ℕ) {base cutoff : ℕ}
    (hb : 0<base) (hc : ∀i:Fin cutoff,p.coeff i.val<base) (k:Fin cutoff) :
    digit base (p.eval base % base^cutoff) k.val = p.coeff k.val := by
  rw [eval_mod_eq_prefix,digit_mod_pow k.isLt]
  exact digit_pack hb _ hc k

/-- Acceptance of a literal packed residue is sufficient, once the source
coefficient bound has been proved. The producer itself is not trusted. -/
theorem accepted_residue_coeff (p : Polynomial ℕ) {base cutoff packed : ℕ}
    (hb : 0<base) (hc : ∀i:Fin cutoff,p.coeff i.val<base)
    (accepted : p.eval base % base^cutoff=packed) (k:Fin cutoff) :
    p.coeff k.val=digit base packed k.val := by
  rw [←accepted]
  exact (digit_eval_of_prefix_bound p hb hc k).symm

#print axioms eval_mod_eq_prefix
#print axioms digit_eval_of_prefix_bound
#print axioms accepted_residue_coeff
end SubmittedGenus.RawGraph.PackedAcceptance
