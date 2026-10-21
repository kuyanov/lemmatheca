import Lemmatheca.CraigInterpolation.Formula
import Lemmatheca.PropositionalLogic.Propositional

namespace Lemmatheca.Entry.CraigInterpolation
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.ChangingLanguages
open Lemmatheca.MathematicalLogic.CraigInterpolation
open Lemmatheca.MathematicalLogic.Propositional
universe u v w
noncomputable section
local instance {α : Type*} : DecidableEq α := Classical.decEq _

/-- The literal two-value forgetting operation on existing propositional formulas. -/
def forgetAtom {α : Type w} (p : α) (A : PropFormula α) : PropFormula α :=
  .disj (subst (fun a => if a = p then .falsum else .atom a) A)
    (subst (fun a => if a = p then verum else .atom a) A)

theorem forgetting_semantics {α : Type w} (p : α) (A : PropFormula α) (v : α → Bool) :
    eval v (forgetAtom p A) = true ↔
      ∃ b : Bool, eval (Function.update v p b) A = true := by
  have h (b : Bool) :
      (fun a => eval v (if a = p then (if b then verum else .falsum) else .atom a)) =
        Function.update v p b := by
    funext a
    by_cases ha : a = p
    · subst a
      cases b <;> simp [eval, verum]
    · simp [ha, eval]
  simp only [forgetAtom, eval, eval_subst, Bool.or_eq_true]
  constructor
  · rintro (hf | ht)
    · exact ⟨false, by simpa only [← h false, Bool.false_eq_true, ite_false] using hf⟩
    · exact ⟨true, by simpa only [← h true, ite_true] using ht⟩
  · rintro ⟨b, hb⟩
    cases b
    · exact Or.inl (by simpa only [← h false, Bool.false_eq_true, ite_false] using hb)
    · exact Or.inr (by simpa only [← h true, ite_true] using hb)

theorem propositional_example {α : Type w} (p q r : α) :
    (∀ v, eval v (.conj (.atom p) (.atom q)) = true → eval v (.atom q) = true) ∧
    (∀ v, eval v (.atom q) = true → eval v (.disj (.atom q) (.atom r)) = true) ∧
    atoms (.atom q) ⊆ atoms (.conj (.atom p) (.atom q)) ∩
      atoms (.disj (.atom q) (.atom r)) := by
  simp only [eval, Bool.and_eq_true, Bool.or_eq_true, atoms]
  exact ⟨fun _ h => h.2, fun _ h => Or.inl h, by simp⟩

variable {L : Language.{u,v}}

/-- The actual equality-only sentence asserting two distinct witnesses. -/
def twoObjects : L.Sentence :=
  ((BoundedFormula.equal (.var (.inr (0 : Fin 2))) (.var (.inr (1 : Fin 2))))).not.ex.ex

/-- Inequality of the two named constant terms. -/
def constantsDiffer (c d : L.Constants) : L.Sentence :=
  ((c.term : L.Term Empty).equal d.term).not

theorem twoObjects_realize (M : Type w) [L.Structure M] :
    M ⊨ (twoObjects : L.Sentence) ↔ ∃ x y : M, x ≠ y := by
  simp [twoObjects, Sentence.Realize, Formula.Realize, BoundedFormula.Realize, Term.realize, Fin.snoc]

theorem equality_only_interpolant (c d : L.Constants) :
    SentenceInterpolant (constantsDiffer c d) twoObjects twoObjects := by
  refine ⟨Theory.models_sentence_iff.mpr ?_, Theory.models_sentence_iff.mpr ?_, ?_⟩
  · intro M
    have h := Theory.realize_sentence_of_mem (M := M) ({constantsDiffer c d} : L.Theory)
      (Set.mem_singleton _)
    apply (twoObjects_realize M).mpr
    refine ⟨(c.term : L.Term Empty).realize default, (d.term : L.Term Empty).realize default, ?_⟩
    simpa [constantsDiffer, Sentence.Realize] using h
  · intro M
    exact Theory.realize_sentence_of_mem ({twoObjects} : L.Theory) (Set.mem_singleton _)
  · simp [twoObjects, formulaSymbols, termSymbols]

theorem equality_only_not_valid_interpolant (c d : L.Constants) :
    ¬ ∃ θ : L.Sentence,
      SentenceInterpolant (constantsDiffer c d) twoObjects θ ∧
        ((∅ : L.Theory) ⊨ᵇ θ) := by
  rintro ⟨θ, hθ, hv⟩
  let M := ULift.{max u v} Unit
  let : L.Structure M := { funMap := fun _ _ => ⟨()⟩, RelMap := fun _ _ => False }
  have ht : M ⊨ θ := (Theory.models_sentence_iff.mp hv) (Theory.ModelType.of ∅ M)
  let : M ⊨ ({θ} : L.Theory) := Theory.model_singleton_iff.mpr ht
  have ha : M ⊨ (twoObjects : L.Sentence) :=
    (Theory.models_sentence_iff.mp hθ.2.1) (Theory.ModelType.of {θ} M)
  obtain ⟨x, y, hxy⟩ := (twoObjects_realize M).mp ha
  exact hxy (Subsingleton.elim _ _)

/-- Quantifying the one variable in a unary predicate atom. -/
def somePredicate (P : L.Relations 1) : L.Sentence :=
  (BoundedFormula.rel P (fun _ => .var (.inr (0 : Fin 1)))).ex

def allPredicate (P : L.Relations 1) : L.Sentence :=
  (BoundedFormula.rel P (fun _ => .var (.inr (0 : Fin 1)))).all

/-- The private function remains in the premise, not in the interpolant. -/
def allFunctionImages (f : L.Functions 1) (P : L.Relations 1) : L.Sentence :=
  (BoundedFormula.rel P (fun _ => .func f (fun _ => .var (.inr (0 : Fin 1))))).all

theorem private_function_interpolant (f : L.Functions 1) (P Q : L.Relations 1) :
    SentenceInterpolant (allFunctionImages f P)
      ((somePredicate P) ⊔ allPredicate Q) (somePredicate P) := by
  refine ⟨Theory.models_sentence_iff.mpr ?_, Theory.models_sentence_iff.mpr ?_, ?_⟩
  · intro M
    have h := Theory.realize_sentence_of_mem (M := M) ({allFunctionImages f P} : L.Theory)
      (Set.mem_singleton _)
    have hp : ∀ x : M, Structure.RelMap P (fun _ => Structure.funMap f (fun _ => x)) := by
      simpa [allFunctionImages, Sentence.Realize, Formula.Realize, BoundedFormula.Realize, Term.realize, Fin.snoc] using h
    have hs : ∃ y : M, Structure.RelMap P (fun _ => y) :=
      ⟨Structure.funMap f (fun _ => Classical.choice (inferInstance : Nonempty M)), hp _⟩
    simpa [somePredicate, Sentence.Realize, Formula.Realize, BoundedFormula.Realize, Term.realize, Fin.snoc] using hs
  · intro M
    apply (Sentence.realize_sup M).mpr
    exact Or.inl (Theory.realize_sentence_of_mem ({somePredicate P} : L.Theory)
      (Set.mem_singleton _))
  · change formulaSymbols (somePredicate P) ⊆ formulaSymbols (allFunctionImages f P) ∩
      formulaSymbols ((somePredicate P).not.imp (allPredicate Q))
    simp [somePredicate, allFunctionImages, allPredicate, formulaSymbols, termSymbols]

theorem endpoint_interpolants (P : L.Relations 1) :
    SentenceInterpolant (allPredicate P) (somePredicate P) (allPredicate P) ∧
    SentenceInterpolant (allPredicate P) (somePredicate P) (somePredicate P) := by
  have hc : ({allPredicate P} : L.Theory) ⊨ᵇ somePredicate P := by
    apply Theory.models_sentence_iff.mpr
    intro M
    have h := Theory.realize_sentence_of_mem (M := M) ({allPredicate P} : L.Theory)
      (Set.mem_singleton _)
    have hp : ∀ x : M, Structure.RelMap P (fun _ => x) := by
      simpa [allPredicate, Sentence.Realize, Formula.Realize, BoundedFormula.Realize, Term.realize, Fin.snoc] using h
    have hs : ∃ x : M, Structure.RelMap P (fun _ => x) :=
      ⟨Classical.choice (inferInstance : Nonempty M), hp _⟩
    simpa [somePredicate, Sentence.Realize, Formula.Realize, BoundedFormula.Realize, Term.realize, Fin.snoc] using hs
  have hself (A : L.Sentence) : ({A} : L.Theory) ⊨ᵇ A :=
    Theory.models_sentence_iff.mpr (fun _ => Theory.realize_sentence_of_mem {A}
      (Set.mem_singleton _))
  have hs : formulaSymbols (allPredicate P) = formulaSymbols (somePredicate P) := by
    simp [allPredicate, somePredicate, formulaSymbols, termSymbols]
  exact ⟨⟨hself _, hc, by rw [hs]; exact Finset.subset_inter Finset.Subset.rfl Finset.Subset.rfl⟩,
    ⟨hc, hself _, by rw [hs]; exact Finset.subset_inter Finset.Subset.rfl Finset.Subset.rfl⟩⟩

/-- A one-predicate language for the specified two-element counterexample. -/
def unaryLanguage : Language where
  Functions _ := Empty
  Relations n := PLift (n = 1)

def unaryPredicate : unaryLanguage.Relations 1 := ⟨rfl⟩

/-- On Bool, the predicate holds precisely at true. -/
@[instance_reducible]
def singletonPredicateStructure : unaryLanguage.Structure Bool where
  funMap f := Empty.elim f
  RelMap {n} R xs := xs ⟨0, by have hn := R.down; omega⟩ = true

theorem nonequivalent_endpoints :
    letI := singletonPredicateStructure
    Bool ⊨ somePredicate unaryPredicate ∧ ¬ (Bool ⊨ allPredicate unaryPredicate) := by
  let := singletonPredicateStructure
  simp only [somePredicate, allPredicate, Sentence.Realize, Formula.Realize, BoundedFormula.realize_ex, BoundedFormula.realize_all]
  change (∃ b : Bool, b = true) ∧ ¬ (∀ b : Bool, b = true)
  exact ⟨⟨true, rfl⟩, fun h => Bool.noConfusion (h false)⟩
end
end Lemmatheca.Entry.CraigInterpolation
