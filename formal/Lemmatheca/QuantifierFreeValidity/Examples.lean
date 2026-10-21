import Lemmatheca.QuantifierFreeValidity.Naming
import Lemmatheca.QuantifierFreeValidity.Convexity

namespace Lemmatheca.Entry.QuantifierFreeValidity
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.QuantifierFreeValidity

/-- Two constants and one unary predicate, with their actual arities. -/
def exampleFunctions : ℕ → Type
  | 0 => Fin 2
  | _ + 1 => Empty

def exampleRelations : ℕ → Type
  | 1 => Unit
  | 0 | _ + 2 => Empty

def exampleLanguage : Language := ⟨exampleFunctions, exampleRelations⟩

instance exampleFunctionsDecidableEq (n : ℕ) : DecidableEq (exampleLanguage.Functions n) := by
  cases n with
  | zero => exact inferInstanceAs (DecidableEq (Fin 2))
  | succ _ => exact inferInstanceAs (DecidableEq Empty)

instance exampleRelationsDecidableEq (n : ℕ) : DecidableEq (exampleLanguage.Relations n) := by
  cases n with
  | zero => exact inferInstanceAs (DecidableEq Empty)
  | succ n =>
    cases n with
    | zero => exact inferInstanceAs (DecidableEq Unit)
    | succ _ => exact inferInstanceAs (DecidableEq Empty)

def constant (i : Fin 2) : Lemmatheca.MathematicalLogic.GroundEquality.GroundTerm exampleLanguage := .func (l := 0) i Fin.elim0
abbrev a := constant 0
abbrev b := constant 1

def predicateAtom (t : Lemmatheca.MathematicalLogic.GroundEquality.GroundTerm exampleLanguage) : Atom exampleLanguage :=
  .rel (arity := 1) () (fun _ => t)

def conflictingRow : Problem exampleLanguage :=
  {(true, .equal a b), (true, predicateAtom a), (false, predicateAtom b)}

def congruenceImplication : exampleLanguage.Sentence :=
  ((Atom.equal a b).formula ⊓ (predicateAtom a).formula).imp (predicateAtom b).formula

def independentValuation (atom : Atom exampleLanguage) : Bool :=
  decide (atom = .equal a b ∨ atom = predicateAtom a)

theorem conflicting_row_rejected : literalTest conflictingRow = false := by
  decide +kernel

theorem congruence_implication_valid (M : Type*) [exampleLanguage.Structure M] :
    congruenceImplication.Realize M := by
  rw [congruenceImplication, Sentence.realize_imp, Sentence.realize_inf]
  change ((Atom.equal a b).Realize M ∧ (predicateAtom a).Realize M) → (predicateAtom b).Realize M
  rw [equal_truth]
  rintro ⟨he, hp⟩
  apply (relation_truth (L := exampleLanguage) (n := 1) () (fun _ => b) M).mpr
  have hv : (fun _ : Fin 1 => a.realize (Empty.elim : Empty → M)) =
      (fun _ : Fin 1 => b.realize (Empty.elim : Empty → M)) := funext fun _ => he
  rw [← hv]
  exact (relation_truth (L := exampleLanguage) (n := 1) () (fun _ => a) M).mp hp

private theorem groundTerm_embed (t : Lemmatheca.MathematicalLogic.GroundEquality.GroundTerm exampleLanguage) :
    groundTerm (t.relabel Sum.inl) = t := by
  rw [groundTerm, Term.relabel_relabel]
  have he : (Sum.elim Empty.elim Fin.elim0 ∘ (Sum.inl : Empty → Empty ⊕ Fin 0)) = id :=
    Subsingleton.elim _ _
  rw [he, Term.relabel_id]

private theorem skeleton_atom (atom : Atom exampleLanguage) : skeleton atom.formula = .atom atom := by
  cases atom with
  | equal t s => simp only [Atom.formula, skeleton.eq_2, groundTerm_embed]
  | rel R ts => simp only [Atom.formula, skeleton.eq_3, groundTerm_embed]

theorem independent_row_falsifies :
    Lemmatheca.MathematicalLogic.Propositional.eval independentValuation
      (skeleton congruenceImplication) = false := by
  change Lemmatheca.MathematicalLogic.Propositional.eval independentValuation
    (skeleton ((((Atom.equal a b).formula.imp ((predicateAtom a).formula.imp .falsum)).imp .falsum).imp
      (predicateAtom b).formula)) = false
  simp only [skeleton.eq_4, skeleton.eq_1, skeleton_atom,
    Lemmatheca.MathematicalLogic.Propositional.eval]
  decide

/-- One domain element, with a chosen truth value for the unary predicate. -/
@[instance_reducible] def onePointStructure (truth : Bool) : exampleLanguage.Structure Unit where
  funMap := fun {n} f _ => match n, f with
    | 0, _ => ()
    | _ + 1, e => nomatch e
  RelMap := fun {n} R _ => match n, R with
    | 1, _ => truth = true
    | 0, e => nomatch e
    | _ + 2, e => nomatch e

def predicateFormula : exampleLanguage.Formula (Fin 1) :=
  .rel (l := 1) () (fun _ => .var (.inl 0))

def tautologyFormula := predicateFormula ⊔ predicateFormula.not
def contradictionFormula := predicateFormula ⊓ predicateFormula.not

theorem predicate_sentence_satisfiable :
    letI := onePointStructure true
    (universalClosure predicateFormula).Realize Unit ∧
      (universalClosure tautologyFormula).Realize Unit := by
  let : exampleLanguage.Structure Unit := onePointStructure true
  constructor
  · apply (universalClosure_truth predicateFormula Unit).mpr
    intro _a
    rfl
  · apply (universalClosure_truth tautologyFormula Unit).mpr
    intro a
    rw [tautologyFormula, Formula.realize_sup, Formula.realize_not]
    exact Classical.em _

theorem predicate_sentence_countermodel :
    letI := onePointStructure false
    ¬(universalClosure predicateFormula).Realize Unit := by
  let : exampleLanguage.Structure Unit := onePointStructure false
  intro h
  have hp := (universalClosure_truth predicateFormula Unit).mp h (fun _ => ())
  exact Bool.false_ne_true hp

theorem validity_and_satisfiability_tests :
    universalTest predicateFormula = false ∧ universalTest tautologyFormula = true ∧
      existentialTest contradictionFormula = false := by
  have hq : predicateFormula.IsQF := (BoundedFormula.IsAtomic.rel _ _).isQF
  refine ⟨?_, ?_, ?_⟩
  · apply Bool.eq_false_iff.mpr
    intro h
    exact predicate_sentence_countermodel
      ((universalTest_correct predicateFormula hq).mp h Unit (onePointStructure false) inferInstance)
  · apply (universalTest_correct tautologyFormula (hq.sup hq.not)).mpr
    intro M inst hne
    let : exampleLanguage.Structure M := inst
    let : Nonempty M := hne
    apply (universalClosure_truth tautologyFormula M).mpr
    intro a
    rw [tautologyFormula, Formula.realize_sup, Formula.realize_not]
    exact Classical.em _
  · apply Bool.eq_false_iff.mpr
    intro h
    obtain ⟨M, inst, _hne, a, ha⟩ :=
      (existentialTest_correct contradictionFormula (hq.inf hq.not)).mp h
    let : exampleLanguage.Structure M := inst
    rw [contradictionFormula, Formula.realize_inf, Formula.realize_not] at ha
    exact ha.2 ha.1

end Lemmatheca.Entry.QuantifierFreeValidity
