import Results.Genus.CapFourMass.IntervalTailSyntax

namespace SubmittedGenus.CapFourMass.Interval
open Expr TailSyntax

/-- One original parity class, including its exact full-feedback prefactor. -/
def pureTerm (P : ℕ) (u v : Fin 2) : Expr :=
  z^8*mass*T*(invPower beta (v.val+1)*parityPower t u v*parityMult v/(etaE*(1-J0))*
    H P u v pureAExpr pureBExpr)

theorem pure_eq_four (P : ℕ) : closedReal (TailSyntax.pure P)=
    closedReal (pureTerm P 0 0)+closedReal (pureTerm P 0 1)+
      closedReal (pureTerm P 1 0)+closedReal (pureTerm P 1 1) := by
  simp only [closedReal,TailSyntax.pure,pureTerm,TailSyntax.sumParity,real_add,real_mul]
  ring

end SubmittedGenus.CapFourMass.Interval
