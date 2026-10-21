import Lemmatheca.DpllSatisfiability.DpllSatisfiability

namespace Lemmatheca.Entry.DpllSatisfiability
open MathematicalLogic.Propositional MathematicalLogic.DpllSatisfiability
universe u
variable {α : Type u} [DecidableEq α]
variable (p q r : α)

def unitExample : Cnf α :=
  [[⟨p,true⟩], [⟨p,false⟩,⟨q,true⟩], [⟨q,false⟩,⟨r,true⟩], [⟨r,false⟩]]
def branchExample : Cnf α :=
  [[⟨p,false⟩,⟨q,true⟩], [⟨p,false⟩,⟨q,false⟩], [⟨p,true⟩,⟨q,true⟩]]

theorem unit_trace (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    setting p true (unitExample p q r) =
      [[⟨q,true⟩], [⟨q,false⟩,⟨r,true⟩], [⟨r,false⟩]] ∧
    setting q true (setting p true (unitExample p q r)) = [[⟨r,true⟩],[⟨r,false⟩]] ∧
    setting r true (setting q true (setting p true (unitExample p q r))) = [[]] ∧
    UnitChain (unitExample p q r) [⟨p,true⟩,⟨q,true⟩,⟨r,true⟩] ∧
    ¬ Sat (unitExample p q r) := by
  have h1 : setting p true (unitExample p q r) =
      [[⟨q,true⟩], [⟨q,false⟩,⟨r,true⟩], [⟨r,false⟩]] := by
    simp [setting, unitExample, PropLiteral.mk.injEq, hpq, hpr, Ne.symm hpq, Ne.symm hpr]
  have h2 : setting q true (setting p true (unitExample p q r)) =
      [[⟨r,true⟩],[⟨r,false⟩]] := by
    rw [h1]
    simp [setting, PropLiteral.mk.injEq, hqr, Ne.symm hqr]
  have h3 : setting r true (setting q true (setting p true (unitExample p q r))) = [[]] := by
    rw [h2]; simp [setting]
  have hrun : UnitChain (unitExample p q r) [⟨p,true⟩,⟨q,true⟩,⟨r,true⟩] := by
    simp only [UnitChain]
    rw [h2,h1]
    simp [unitExample]
  refine ⟨h1,h2,h3,hrun,?_⟩
  rintro ⟨v,hv⟩
  have ht := unit_chain_forced hrun v hv (⟨r,true⟩ : PropLiteral α) (by simp)
  have hf := unit_forced (p := r) (b := false) (by simp [unitExample]) v hv
  exact Bool.noConfusion (ht.symm.trans hf)


theorem pure_not_forced (hpq : p ≠ q) :
    let Γ : Cnf α := [[⟨p,true⟩,⟨q,true⟩]]
    Pure ⟨p,true⟩ Γ ∧
    Models (Function.update (fun _ => false) q true) Γ ∧
    Function.update (fun _ => false) q true p = false ∧
    setting p true Γ = [] ∧ ¬ Models (fun _ => false) Γ := by
  simp [MathematicalLogic.DpllSatisfiability.Pure, occurs, Models, MathematicalLogic.TseitinEncoding.ListModels, setting,
    PropLiteral.mk.injEq, hpq]


theorem branch_trace (hpq : p ≠ q) :
    setting p true (branchExample p q) = [[⟨q,true⟩],[⟨q,false⟩]] ∧
    solve [q] (setting p true (branchExample p q)) = none ∧
    setting p false (branchExample p q) = [[⟨q,true⟩]] ∧
    solve [p,q] (branchExample p q) =
      some (Function.update (Function.update (fun _ => false) q true) p false) := by
  simp [branchExample, setting, solve, preferred, occurs, restore,
    PropLiteral.mk.injEq, hpq, Ne.symm hpq]

end Lemmatheca.Entry.DpllSatisfiability
