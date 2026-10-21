import Lemmatheca.GroundEquality.Models

namespace Lemmatheca.Entry.GroundEquality

open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.GroundEquality

/-- Three constants and one unary function, with their genuine arities. -/
def ExampleFunctions : ℕ → Type
  | 0 => Fin 3
  | 1 => Unit
  | _ + 2 => Empty

def exampleLanguage : Language := ⟨ExampleFunctions, fun _ => Empty⟩

instance exampleFunctionsDecidableEq (n : ℕ) : DecidableEq (exampleLanguage.Functions n) := by
  cases n with
  | zero => exact inferInstanceAs (DecidableEq (Fin 3))
  | succ n =>
    cases n with
    | zero => exact inferInstanceAs (DecidableEq Unit)
    | succ _ => exact inferInstanceAs (DecidableEq Empty)

def constant (i : Fin 3) : GroundTerm exampleLanguage :=
  .func (l := 0) i Fin.elim0

def applyF (t : GroundTerm exampleLanguage) : GroundTerm exampleLanguage :=
  .func (l := 1) () (fun _ => t)

abbrev a := constant 0
abbrev b := constant 1
abbrev c := constant 2

@[instance_reducible] def twoPointStructure (constants : Fin 3 → Fin 2) :
    exampleLanguage.Structure (Fin 2) where
  funMap := fun {n} f _ => match n, f with
    | 0, i => constants i
    | 1, _ => 0
    | _ + 2, e => nomatch e
  RelMap := fun r _ => nomatch r

@[instance_reducible] def representativeStructure : exampleLanguage.Structure (Fin 2) :=
  twoPointStructure (fun i => if i = 2 then 1 else 0)

@[instance_reducible] def noninjectiveStructure : exampleLanguage.Structure (Fin 2) :=
  twoPointStructure (fun i => if i = 1 then 1 else 0)

def representativeProblem : Problem exampleLanguage :=
  ⟨{(a, b)}, {(applyF a, c)}⟩

def noninjectiveProblem : Problem exampleLanguage :=
  ⟨{(applyF a, applyF b)}, {(a, b)}⟩

def conflictingProblem : Problem exampleLanguage :=
  ⟨{(a, b)}, {(applyF a, applyF b)}⟩

def cyclicProblem : Problem exampleLanguage := ⟨{(a, applyF a)}, ∅⟩

theorem representative_support :
    support representativeProblem = {a, b, c, applyF a} ∧
      applyF b ∉ support representativeProblem := by
  decide

theorem representative_input_classes :
    (a, b) ∈ closure (support representativeProblem) representativeProblem.equations := by
  exact equations_subset_closure _ _ (by simp [representativeProblem])

theorem representative_function_value
    (hb : b ∈ support representativeProblem) (hfa : applyF a ∈ support representativeProblem) :
    functionMap (support representativeProblem) representativeProblem.equations
      (equations_supported representativeProblem) (support_closed representativeProblem)
      (n := 1) () (fun _ => classOf (support representativeProblem)
        representativeProblem.equations (equations_supported representativeProblem) b hb) =
      classOf (support representativeProblem) representativeProblem.equations
        (equations_supported representativeProblem) (applyF a) hfa := by
  have ha : a ∈ support representativeProblem := by
    rw [representative_support.1]
    simp
  have hab := (classOf_eq_iff (support representativeProblem) representativeProblem.equations
    (equations_supported representativeProblem) a b ha hb).mpr representative_input_classes
  exact functionMap_of_represented (support representativeProblem) representativeProblem.equations
    (equations_supported representativeProblem) (support_closed representativeProblem)
    (n := 1) () _ ⟨fun _ => a, hfa, fun _ => hab⟩

theorem representative_solution :
    @Satisfies _ representativeProblem (Fin 2) representativeStructure := by
  constructor
  · intro p hp
    have heq : p = (a, b) := by simpa [representativeProblem] using hp
    subst p
    rfl
  · intro p hp
    have heq : p = (applyF a, c) := by simpa [representativeProblem] using hp
    subst p
    decide

theorem noninjective_solution :
    @Satisfies _ noninjectiveProblem (Fin 2) noninjectiveStructure := by
  constructor
  · intro p hp
    have heq : p = (applyF a, applyF b) := by simpa [noninjectiveProblem] using hp
    subst p
    rfl
  · intro p hp
    have heq : p = (a, b) := by simpa [noninjectiveProblem] using hp
    subst p
    decide

theorem conflicting_no_model : ¬ HasModel conflictingProblem := by
  rintro ⟨M, inst, _, hM⟩
  let : exampleLanguage.Structure M := inst
  have hab : a.realize Empty.elim = b.realize (Empty.elim : Empty → M) :=
    hM.1 (a, b) (by simp [conflictingProblem])
  apply hM.2 (applyF a, applyF b) (by simp [conflictingProblem])
  change Structure.funMap (L := exampleLanguage) (n := 1) ()
    (fun _ => a.realize (Empty.elim : Empty → M)) =
    Structure.funMap (L := exampleLanguage) (n := 1) ()
      (fun _ => b.realize (Empty.elim : Empty → M))
  rw [hab]

@[instance_reducible] def singletonStructure : exampleLanguage.Structure Unit where
  funMap := fun _ _ => ()
  RelMap := fun _ _ => False

theorem cyclic_solution : @Satisfies _ cyclicProblem Unit singletonStructure := by
  constructor
  · intro p _
    exact Subsingleton.elim _ _
  · simp [cyclicProblem]

/-- Iterating the same unary term constructor never requires new values at a fixed point. -/
def iterateF (n : ℕ) : GroundTerm exampleLanguage := (applyF^[n]) a

theorem cyclic_iterates (M : Type*) [exampleLanguage.Structure M]
    (h : a.realize Empty.elim = (applyF a).realize (Empty.elim : Empty → M)) (n : ℕ) :
    (iterateF n).realize Empty.elim = a.realize (Empty.elim : Empty → M) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [iterateF, Function.iterate_succ_apply']
    change Structure.funMap (L := exampleLanguage) (n := 1) ()
      (fun _ => ((applyF^[n]) a).realize Empty.elim) = _
    rw [show ((applyF^[n]) a).realize Empty.elim = a.realize (Empty.elim : Empty → M) from ih]
    exact h.symm

end Lemmatheca.Entry.GroundEquality

namespace Lemmatheca.MathematicalLogic.GroundEquality

open FirstOrder FirstOrder.Language

universe u v
variable {L : Language.{u, v}} [∀ n, DecidableEq (L.Functions n)]

/-- The empty input, independently of whether the language has any ground terms. -/
def emptyProblem : Problem L := ⟨∅, ∅⟩

theorem empty_support : support (emptyProblem : Problem L) = ∅ := by
  simp [support, emptyProblem]

theorem empty_carrier_card :
    Nat.card (Carrier (support (emptyProblem : Problem L)) emptyProblem.equations
      (equations_supported emptyProblem)) = 1 := by
  have no_class : ∀ q : Quotient (termSetoid (support (emptyProblem : Problem L))
      emptyProblem.equations (equations_supported emptyProblem)), False := by
    intro q
    obtain ⟨t, rfl⟩ := Quotient.mk_surjective q
    have ht := t.property
    exact (Finset.eq_empty_iff_forall_notMem.mp empty_support) _ ht
  have only_default : ∀ x : Carrier (support (emptyProblem : Problem L))
      emptyProblem.equations (equations_supported emptyProblem), x = none := by
    intro x
    cases x with
    | none => rfl
    | some q => exact (no_class q).elim
  apply Nat.card_eq_one_iff_unique.mpr
  exact ⟨⟨fun x y => (only_default x).trans (only_default y).symm⟩, inferInstance⟩

theorem empty_function_value {n : ℕ} (f : L.Functions n)
    (xs : Fin n → Carrier (support (emptyProblem : Problem L)) emptyProblem.equations
      (equations_supported emptyProblem)) :
    functionMap (support (emptyProblem : Problem L)) emptyProblem.equations
      (equations_supported emptyProblem) (support_closed emptyProblem) f xs = none := by
  apply functionMap_of_unrepresented
  refine ⟨fun a => ?_⟩
  have ht := a.retained
  exact (Finset.eq_empty_iff_forall_notMem.mp empty_support) _ ht

end Lemmatheca.MathematicalLogic.GroundEquality
