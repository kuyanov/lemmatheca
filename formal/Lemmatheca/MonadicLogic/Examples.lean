import Lemmatheca.MonadicLogic.Decision
import Lemmatheca.ExistentialUniversalSentences.Examples

namespace Lemmatheca.Entry.MonadicLogic
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic
open Lemmatheca.MathematicalLogic.MonadicLogic

/-- Predicate application in the same bounded first-order syntax as the main theorem. -/
def atom {k n : ℕ} (i : Fin k) (j : Fin n) : (lang k).BoundedFormula Empty n :=
  .rel (predicate k i) (fun _ => .var (.inr j))

private def conjunction {k n : ℕ} (xs : List ((lang k).BoundedFormula Empty n)) :
    (lang k).BoundedFormula Empty n := xs.foldr (fun φ ψ => φ ⊓ ψ) ⊤

/-- The matrix lists predicate atoms, followed by all ordered distinct pairs of inequalities. -/
private def copiesMatrix (s : ℕ) : (lang 1).BoundedFormula Empty s :=
    conjunction ((List.finRange s).map (atom 0) ++
      (List.finRange s).flatMap fun i => (List.finRange s).map fun j =>
        if i = j then ⊤ else (BoundedFormula.equal (.var (.inr i)) (.var (.inr j)) : (lang 1).BoundedFormula Empty s).not)

def manyCopies (s : ℕ) : (lang 1).Sentence :=
  ExistentialUniversalSentences.exBlock 0 (arities 1) s (copiesMatrix s)

def oneWitness : (lang 1).Sentence := (atom 0 (0 : Fin 1)).ex

def oppositeProfiles : (lang 1).Sentence :=
  ((atom 0 (0 : Fin 2)).iff (atom 0 (1 : Fin 2)).not).ex.all

private theorem atom_realize {k n : ℕ} {M : Type*} [(lang k).Structure M]
    (i : Fin k) (j : Fin n) (v : Empty → M) (a : Fin n → M) :
    (atom i j).Realize v a ↔ Structure.RelMap (predicate k i) (fun _ => a j) := by
  rfl

private theorem conjunction_realize {k n : ℕ} {M : Type*} [(lang k).Structure M]
    (xs : List ((lang k).BoundedFormula Empty n)) (a : Fin n → M) :
    (conjunction xs).Realize Empty.elim a ↔ ∀ φ ∈ xs, φ.Realize Empty.elim a := by
  induction xs with
  | nil => simp [conjunction, BoundedFormula.realize_top]
  | cons φ xs ih =>
    have hc : conjunction (φ :: xs) = φ ⊓ conjunction xs := rfl
    rw [hc,BoundedFormula.realize_inf,ih]
    simp

private theorem copiesMatrix_realize {M : Type*} [(lang 1).Structure M] (s : ℕ)
    (a : Fin s → M) :
    (copiesMatrix s).Realize Empty.elim a ↔
      (∀ i, Structure.RelMap (predicate 1 0) (fun _ => a i)) ∧ Function.Injective a := by
  classical
  rw [copiesMatrix,conjunction_realize,List.forall_mem_append]
  simp only [List.forall_mem_map,List.forall_mem_flatMap,List.mem_finRange,forall_true_left,
    atom_realize]
  constructor
  · rintro ⟨hp,hd⟩
    refine ⟨hp,?_⟩
    intro i j hij
    by_contra hne
    have hneq : a i ≠ a j := by
      simpa [hne,BoundedFormula.Realize,Term.realize] using hd i j
    exact hneq hij
  · rintro ⟨hp,hi⟩
    refine ⟨hp,fun i j => ?_⟩
    by_cases h : i = j
    · simp [h,BoundedFormula.realize_top]
    · have hneq : a i ≠ a j := fun he => h (hi he)
      simpa [h,BoundedFormula.Realize,Term.realize] using hneq

theorem manyCopies_realize {M : Type*} [(lang 1).Structure M] (s : ℕ) :
    M ⊨ manyCopies s ↔
      ∃ a : Fin s → M, (∀ i, Structure.RelMap (predicate 1 0) (fun _ => a i)) ∧
        Function.Injective a := by
  change M ⊨ ExistentialUniversalSentences.sentence 0 (arities 1)
    (m := s) (n := 0) (copiesMatrix s) ↔ _
  rw [ExistentialUniversalSentences.sentence_realize]
  simp [ExistentialUniversalSentences.MatrixTrue, Fin.append_right_nil _ _ rfl,
    copiesMatrix_realize]

theorem oneWitness_realize {M : Type*} [(lang 1).Structure M] :
    M ⊨ oneWitness ↔ ∃ x : M, Structure.RelMap (predicate 1 0) (fun _ => x) := by
  simp [oneWitness, Sentence.Realize, Formula.Realize, BoundedFormula.realize_ex, atom_realize, Fin.snoc]

theorem oppositeProfiles_realize {M : Type*} [(lang 1).Structure M] :
    M ⊨ oppositeProfiles ↔
      ∀ x : M, ∃ y : M,
        (Structure.RelMap (predicate 1 0) (fun _ => x) ↔
         ¬ Structure.RelMap (predicate 1 0) (fun _ => y)) := by
  simp [oppositeProfiles, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_ex, BoundedFormula.realize_iff, BoundedFormula.realize_not,
    atom_realize, Fin.snoc]

theorem same_profile_equality_counterexample :
    (letI := structureOfPredicates (fun (_ : Fin 1) (_ : Bool) => True)
     Bool ⊨ manyCopies 2) ∧
    (letI := structureOfPredicates (fun (_ : Fin 1) (_ : Unit) => True)
     ¬ Unit ⊨ manyCopies 2) := by
  constructor
  · let := structureOfPredicates (fun (_ : Fin 1) (_ : Bool) => True)
    rw [manyCopies_realize]
    exact ⟨fun i : Fin 2 => i.val == 1,fun _ => True.intro,by decide⟩
  · let := structureOfPredicates (fun (_ : Fin 1) (_ : Unit) => True)
    rw [manyCopies_realize]
    rintro ⟨a,_,hi⟩
    have hc := Fintype.card_le_of_injective a hi
    simp at hc

theorem distinct_predicate_witnesses {M : Type*} (P : M → Prop) (s : ℕ) :
    (∃ a : Fin s → M, (∀ i, P (a i)) ∧ ∀ i j, i ≠ j → a i ≠ a j) ↔
      ∃ a : Fin s → M, Function.Injective a ∧ ∀ i, P (a i) := by
  constructor
  · rintro ⟨a,hp,hd⟩
    refine ⟨a,?_,hp⟩
    intro i j hij
    by_contra hne
    exact hd i j hne hij
  · rintro ⟨a,hi,hp⟩
    exact ⟨a,hp,fun i j hne hij => hne (hi hij)⟩

theorem same_profile_many_model (s : ℕ) :
    letI := structureOfPredicates (fun (_ : Fin 1) (_ : Fin s) => True)
    Fin s ⊨ manyCopies s := by
  let := structureOfPredicates (fun (_ : Fin 1) (_ : Fin s) => True)
  rw [manyCopies_realize]
  exact ⟨id,fun _ => True.intro,Function.injective_id⟩

theorem oneWitness_bound : bound oneWitness = 2 := by rfl

theorem singleton_witness :
    letI := structureOfPredicates (fun (_ : Fin 1) (_ : Unit) => True)
    Unit ⊨ oneWitness := by
  let := structureOfPredicates (fun (_ : Fin 1) (_ : Unit) => True)
  rw [oneWitness_realize]
  exact ⟨(),True.intro⟩

theorem opposite_profile_model :
    letI := structureOfPredicates (fun (_ : Fin 1) (x : Bool) => x = true)
    Bool ⊨ oppositeProfiles := by
  let := structureOfPredicates (fun (_ : Fin 1) (x : Bool) => x = true)
  rw [oppositeProfiles_realize]
  intro x
  refine ⟨!x,?_⟩
  change (x = true ↔ ¬(!x) = true)
  cases x <;> decide

end Lemmatheca.Entry.MonadicLogic
