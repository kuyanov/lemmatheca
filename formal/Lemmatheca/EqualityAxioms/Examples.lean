import Lemmatheca.EqualityAxioms.EqualityAxioms

namespace Lemmatheca.Entry.EqualityAxioms
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.EqualityAxioms
open Lemmatheca.MathematicalLogic.HerbrandModels

universe u v

/-- An arbitrary old relation truth value on the unique tuple of each arity. -/
@[instance_reducible] def onePointStructure (L : Language.{u, v})
    (p : ∀ {n}, L.Relations n → Prop) : L.Structure PUnit where
  funMap _ _ := PUnit.unit
  RelMap R _ := p R

theorem one_point_axioms (L : Language.{u, v}) (p : ∀ {n}, L.Relations n → Prop) :
    letI := onePointStructure L p
    letI := identityExpansion (L := L) PUnit
    Axioms L PUnit := by
  let := onePointStructure L p
  exact identity_axioms PUnit

theorem one_point_quotient (L : Language.{u, v}) (p : ∀ {n}, L.Relations n → Prop) :
    letI := onePointStructure L p
    letI := identityExpansion (L := L) PUnit
    ∀ h : Axioms L PUnit, Nonempty (QuotientModel h) ∧ Subsingleton (QuotientModel h) := by
  let := onePointStructure L p
  let := identityExpansion (L := L) PUnit
  intro h
  exact ⟨quotient_nonempty h, inferInstance⟩

/-- A concrete actual native formula with two constants and a zero-ary relation. -/
def constantFormula {L : Language.{u, v}} (c d : L.Functions 0) (R : L.Relations 0) : L.Sentence :=
  ((Term.func c Fin.elim0).equal (Term.func d Fin.elim0)) ⊓ R.formula Fin.elim0

theorem constant_example {L : Language.{u, v}} (c d : L.Functions 0) (R : L.Relations 0) :
    letI := onePointStructure L (fun {_} _ => True)
    letI := identityExpansion (L := L) PUnit
    Sentence.Realize PUnit (translate (constantFormula c d R)) := by
  let := onePointStructure L (fun {_} _ => True)
  apply (identity_truth PUnit (constantFormula c d R) Empty.elim default).mpr
  simp [constantFormula, BoundedFormula.Realize, Term.equal, Relations.formula,
    Relations.boundedFormula, Term.realize]
  trivial

theorem one_point_no_inequivalent (L : Language.{u, v}) (p : ∀ {n}, L.Relations n → Prop) :
    letI := onePointStructure L p
    letI := identityExpansion (L := L) PUnit
    ¬ ∃ a b : PUnit, ¬ E (L := L) a b := by
  rintro ⟨a, b, hab⟩
  exact hab (Subsingleton.elim a b)

inductive UnarySymbol : ℕ → Type
  | predicate : UnarySymbol 1

def predicateLanguage : Language where
  Functions _ := Empty
  Relations := UnarySymbol

/-- Total E but a nonconstant old predicate on two actual points. -/
@[instance_reducible] def badStructure : (Extended predicateLanguage).Structure Bool where
  funMap f _ := Empty.elim f
  RelMap R a := match R with
    | .inl .predicate => a 0 = false
    | .inr .equality => True

theorem bad_equivalence_and_functions :
    letI := badStructure
    (∀ a b : Bool, E (L := predicateLanguage) a b) ∧
    (∀ {n} (F : (Fin n → Bool) → Bool) (a b : Fin n → Bool),
      (∀ i, E (L := predicateLanguage) (a i) (b i)) →
        E (L := predicateLanguage) (F a) (F b)) := by
  exact ⟨fun _ _ => trivial, fun _ _ _ _ => trivial⟩

theorem bad_predicate_values :
    letI := badStructure
    Structure.RelMap (L := Extended predicateLanguage) (.inl UnarySymbol.predicate) ![false] ∧
      ¬ Structure.RelMap (L := Extended predicateLanguage) (.inl UnarySymbol.predicate) ![true] := by
  exact ⟨rfl, Bool.noConfusion⟩

/-- The very relation-congruence clause is false under x0=0,x1=1. -/
theorem bad_clause_false :
    letI := badStructure
    ¬ (clauseToFormula (relationClause (L := predicateLanguage) UnarySymbol.predicate)).Realize
      (fun n : ℕ => if n = 0 then false else true) := by
  let := badStructure
  rw [clause_formula_realize]
  simp [ClauseRealize, relationClause, negativePairs, positive, negative, eqAtom,
    oldAtom, leftVariables, rightVariables, Atom.Realize, Structure.RelMap]

theorem bad_not_axioms :
    letI := badStructure
    ¬ Axioms predicateLanguage Bool := by
  let := badStructure
  intro h
  have hv := (h.relations UnarySymbol.predicate ![false] ![true]
    (fun _ => trivial)).mp rfl
  exact Bool.noConfusion hv

end Lemmatheca.Entry.EqualityAxioms
