import Lemmatheca.MathematicalLogic.Resolution
namespace Lemmatheca.Entry.Resolution
open Lemmatheca.MathematicalLogic
open Lemmatheca.MathematicalLogic.Resolution
abbrev p : Fin 3 := 0
abbrev q : Fin 3 := 1
abbrev r : Fin 3 := 2

def switchClauses : ClauseSet (Fin 3) := {{pos p, pos q}, {neg p}, {neg q}}
def eliminatedExample : ClauseSet (Fin 3) := {{pos p, pos q}, {neg p, pos r}, {neg q}}
def switchFormula : PropFormula (Fin 3) :=
  .impl (.conj (.disj (.atom p) (.atom q)) (.neg (.atom p))) (.atom q)
theorem sample_resolvents :
    resolvent p {pos p, neg q, neg r} {neg p, neg q} = {neg q, neg r} ∧
    resolvent p {pos p} {neg p} = ∅ := by
  decide
theorem switch_refutation : Derives switchClauses ∅ := by
  have first : Derives switchClauses (resolvent p {pos p, pos q} {neg p}) :=
    Derives.resolve p (by decide) (by decide)
      (.premise (by decide)) (.premise (by decide))
  have he : resolvent p {pos p, pos q} {neg p} = {pos q} := by decide
  rw [he] at first
  have last : Derives switchClauses (resolvent q {pos q} {neg q}) :=
    Derives.resolve q (by decide) (by decide) first (.premise (by decide))
  have he' : resolvent q {pos q} {neg q} = ∅ := by decide
  exact he' ▸ last
theorem two_pivots :
    resolvent p {pos p, pos q} {neg p, neg q} = {pos q, neg q} ∧
    resolvent q {pos p, pos q} {neg p, neg q} = {pos p, neg p} ∧
    Models (fun a => a == p) ({{pos p, pos q}, {neg p, neg q}} : ClauseSet (Fin 3)) := by
  unfold Models ClauseSat LiteralSat
  decide
theorem elimination_example :
    eliminate p eliminatedExample = {{neg q}, {pos q, pos r}} ∧
    Models (fun a => a == r) (eliminate p eliminatedExample) ∧
    Models (fun a => a != q) eliminatedExample := by
  unfold Models ClauseSat LiteralSat
  decide
theorem switch_negation_cnf :
    SemEquivalent (.neg switchFormula)
      (cnfFormula [[pos p, pos q], [neg p], [neg q]]) ∧
    Tautology switchFormula := by
  constructor
  · intro v
    cases hp : v p <;> cases hq : v q <;>
      simp [switchFormula, cnfFormula, clauseFormula, finiteConj, finiteDisj,
        literalFormula, pos, neg, eval, hp, hq]
  · intro v
    change eval v switchFormula = true
    simp only [switchFormula, eval]
    cases v p <;> cases v q <;> rfl
theorem replacing_parents_loses_information :
    ClauseSat (fun a => a == q) (resolvent p {pos p} {neg p, pos q}) ∧
    ¬ Models (fun a => a == q) ({{pos p}, {neg p, pos q}} : ClauseSet (Fin 3)) := by
  unfold Models ClauseSat LiteralSat
  decide
end Lemmatheca.Entry.Resolution
