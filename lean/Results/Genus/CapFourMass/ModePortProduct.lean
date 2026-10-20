import Results.Genus.CapFourMass.SourcePorts

/-! Complete signed source-mode coefficients as fixed strong-core contractions
against one actual q-mode at each surviving carry port. -/
noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.CapFourMass
open FixedPivot

lemma variable_carry_endpoint_product (N d : ℕ) (hN : d<N)
    (g : Fin d→ℝ) (loop : CarryRepresentative N d hN→ℝ) :
    (∏ c : CarryRepresentative N d hN,
      g c.val*(if c.val=portPartner N d hN c.val then loop c else g (portPartner N d hN c.val)))=
      (∏ a : Fin d,g a)*
        ∏ c : CarryRepresentative N d hN,if c.val=portPartner N d hN c.val then loop c else 1 := by
  have he:=carry_endpoint_product N d hN g (1:ℝ)
  simp only [one_pow,mul_one] at he
  rw [← he,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro c _
  split_ifs <;> simp

def sourcePortMode (N d : ℕ) (hN : d<N) (choice : CarryRepresentative N d hN→Bool) (a : Fin d) : Mode :=
  choiceMode (choice (carryRepresentative N d hN a))

def sourcePortFactor {r N d : ℕ} (hd : 0<d) (hN : d<N)
    (x : Fin (r+d)→Fin 5) (choice : CarryRepresentative N d hN→Bool) (a : Fin d) : ℝ :=
  if a=pivotPort d hd then freeBoundary ⬝ᵥ modeVector (sourcePortMode N d hN choice a) else
    modeRoot (sourcePortMode N d hN choice a)*
      modeVector (sourcePortMode N d hN choice a) (canonicalPortState x a).castSucc/
      halfWeight (canonicalPortState x a).castSucc

def sourceLoopFactor (N d : ℕ) (hN : d<N)
    (choice : CarryRepresentative N d hN→Bool) (c : CarryRepresentative N d hN) : ℝ :=
  if c.val=portPartner N d hN c.val then loopBoundary ⬝ᵥ modeVector (choiceMode (choice c)) else 1

def sourceCarryFactor (N d : ℕ) (hN : d<N) (choice : CarryRepresentative N d hN→Bool) : ℝ :=
  (∏ c : CarryRepresentative N d hN,(modeRoot (choiceMode (choice c)))^(carryTailSize N d hN c-1))*
    ∏ c : CarryRepresentative N d hN,sourceLoopFactor N d hN choice c

lemma canonical_start_mode_factor {r N d : ℕ} (hd : 0<d) (hN : d<N)
    (x : Fin (r+d)→Fin 5) (hx : StableCoreAllowed r (r+d) x)
    (choice : CarryRepresentative N d hN→Bool) (c : CarryRepresentative N d hN) :
    sourceHalf (fun v : Fin 3 => if canonicalStartAllowed x c v then 1 else 0) ⬝ᵥ modeVector (choiceMode (choice c))=
      sourcePortFactor hd hN x choice c.val := by
  unfold canonicalStartAllowed sourcePortFactor sourcePortMode
  rw [carryRepresentative_of_rep]
  exact canonical_port_mode hd x hx c.val _

lemma canonical_finish_mode_factor {r N d : ℕ} (hd : 0<d) (hN : d<N)
    (x : Fin (r+d)→Fin 5) (hx : StableCoreAllowed r (r+d) x)
    (choice : CarryRepresentative N d hN→Bool) (c : CarryRepresentative N d hN) :
    modeVector (choiceMode (choice c)) ⬝ᵥ sourceHalf (fun v : Fin 3 => if canonicalFinishAllowed x c v then 1 else 0)=
      if c.val=portPartner N d hN c.val then loopBoundary ⬝ᵥ modeVector (choiceMode (choice c)) else
        sourcePortFactor hd hN x choice (portPartner N d hN c.val) := by
  rw [dot_comm]
  by_cases hc : c.val=portPartner N d hN c.val
  · simp only [canonicalFinishAllowed,if_pos hc,sourceHalf_loop]
  · simp only [canonicalFinishAllowed,if_neg hc]
    unfold sourcePortFactor sourcePortMode
    rw [carryRepresentative_partner,carryRepresentative_of_rep]
    exact canonical_port_mode hd x hx (portPartner N d hN c.val) _

/-- The exact complete-mode coefficient now has a fixed strong-core sum with
only unary port-mode factors; no absolute value has moved through that sum. -/
theorem sourceCoefficient_eq_port_product {r N d : ℕ} (hd : 0<d) (hN : d<N)
    (choice : CarryRepresentative N d hN→Bool) :
    sourceCoefficient r N d hN choice=sourceCarryFactor N d hN choice*
      ∑ x : Fin (r+d)→Fin 5,
        Polynomial.eval₂ (Nat.castRingHom ℝ) radius (stableCoreTerm r (r+d) x)*
          ∏ a : Fin d,sourcePortFactor hd hN x choice a := by
  rw [sourceCoefficient_eq_symmetric]
  unfold symmetricSourceCoefficient sourceCarryFactor
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : StableCoreAllowed r (r+d) x
  · simp_rw [canonical_start_mode_factor hd hN x hx,canonical_finish_mode_factor hd hN x hx]
    have he : (∏ c : CarryRepresentative N d hN,
        modeRoot (choiceMode (choice c))^(carryTailSize N d hN c-1)*sourcePortFactor hd hN x choice c.val*
          (if c.val=portPartner N d hN c.val then loopBoundary ⬝ᵥ modeVector (choiceMode (choice c)) else
            sourcePortFactor hd hN x choice (portPartner N d hN c.val)))=
        (∏ c : CarryRepresentative N d hN,modeRoot (choiceMode (choice c))^(carryTailSize N d hN c-1))*
        ((∏ a : Fin d,sourcePortFactor hd hN x choice a)*
          ∏ c : CarryRepresentative N d hN,sourceLoopFactor N d hN choice c) := by
      unfold sourceLoopFactor
      rw [← variable_carry_endpoint_product N d hN (sourcePortFactor hd hN x choice)
        (fun c => loopBoundary ⬝ᵥ modeVector (choiceMode (choice c))),← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro c _
      ring
    rw [he]
    ring
  · have hz : Polynomial.eval₂ (Nat.castRingHom ℝ) radius (stableCoreTerm r (r+d) x)=0 := by
      simp only [stableCoreTerm,hx,if_false,Polynomial.eval₂_zero]
    rw [hz,zero_mul,zero_mul,mul_zero]

end SubmittedGenus.CapFourMass
