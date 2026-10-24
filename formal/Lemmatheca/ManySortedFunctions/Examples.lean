import Lemmatheca.ManySortedFunctions.Translation
import Mathlib.Tactic.FinCases

namespace Lemmatheca.Entry.ManySortedFunctions
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.ManySortedFunctions
inductive ListFunction : ℕ → Type
  | nil : ListFunction 0
  | cons : ListFunction 2
  | head : ListFunction 1
def listSignature : Signature where
  Sorts := Bool
  Relations := fun _ => Empty
  profile := fun r => r.elim
  Functions := ListFunction
  input := fun f => match f with
    | .nil => Fin.elim0
    | .cons => ![false,true]
    | .head => fun _ => true
  output := fun f => match f with
    | .nil => true
    | .cons => true
    | .head => false

def listContext : Context listSignature 2 := ![false,true]
def listX : Term listSignature listContext false := .var 0 rfl
def listQ : Term listSignature listContext true := .var 1 rfl
def listNil {n} {γ : Context listSignature n} : Term listSignature γ true :=
  .app (L := listSignature) ListFunction.nil (fun i => Fin.elim0 i)
def listCons {n} {γ : Context listSignature n}
    (t : Term listSignature γ false) (q : Term listSignature γ true) :
    Term listSignature γ true :=
  .app (L := listSignature) ListFunction.cons (Fin.cases t (Fin.cases q (fun i => Fin.elim0 i)))
def listHead {n} {γ : Context listSignature n} (q : Term listSignature γ true) :
    Term listSignature γ false := .app (L := listSignature) ListFunction.head (fun _ => q)
def listTerm : Term listSignature listContext false := listHead (listCons listX listQ)
def listSubstitution : Term.Substitution listContext listContext :=
  Fin.cases (listHead listQ) (Fin.cases (listCons listX listNil) (fun i => Fin.elim0 i))

def listModel : Model listSignature where
  Carrier := fun s => match s with | false => ℕ | true => List ℕ
  nonempty := fun s => by cases s <;> infer_instance
  func := fun f ts => match f with
    | .nil => []
    | .cons => ts 0 :: ts 1
    | .head => (ts 0).headD 0
  rel := fun r => r.elim
def listAssignment : listModel.Assignment listContext :=
  Fin.cases (7 : ℕ) (Fin.cases ([2,5] : List ℕ) (fun i => Fin.elim0 i))
def listPulled : listModel.Assignment listContext :=
  Fin.cases (2 : ℕ) (Fin.cases ([7] : List ℕ) (fun i => Fin.elim0 i))

theorem list_substitution :
    listTerm.subst listSubstitution =
      listHead (listCons (listHead listQ) (listCons listX listNil)) := by
  unfold listTerm listHead listCons listX listQ listSubstitution
  simp only [MathematicalLogic.ManySortedFunctions.Term.subst]
  congr 1
  funext i
  fin_cases i
  congr 1
  funext j
  fin_cases j <;> rfl
theorem list_calculation :
    listModel.pull listSubstitution listAssignment = listPulled ∧
    listModel.eval listAssignment (listTerm.subst listSubstitution) = (2 : ℕ) ∧
    listModel.eval listPulled listTerm = (2 : ℕ) := by
  refine ⟨?_, ?_, ?_⟩
  · funext i
    fin_cases i <;> rfl
  · rfl
  · rfl

def equalitySignature : Signature where
  Sorts := Unit
  Relations := fun _ => Empty
  profile := fun r => r.elim
  Functions := fun _ => Empty
  input := fun f => f.elim
  output := fun f => f.elim
def equalityContext : Context equalitySignature 1 := fun _ => ()
def equalityModel : Model equalitySignature where
  Carrier := fun _ => Bool
  nonempty := fun _ => inferInstance
  func := fun f => f.elim
  rel := fun r => r.elim
def freeEqualsBound : Formula equalitySignature equalityContext :=
  .all () (.equal (.var 0 rfl) (.var 1 rfl))
def capturedTautology : Formula equalitySignature equalityContext :=
  .all () (.equal (.var 1 rfl) (.var 1 rfl))
theorem capture_counterexample (a : equalityModel.Assignment equalityContext) :
    ¬equalityModel.Realize freeEqualsBound a ∧
      equalityModel.Realize capturedTautology a := by
  constructor
  · intro h
    change ∀ x : Bool, a 0 = x at h
    have hf := h false
    have ht := h true
    exact Bool.false_ne_true (hf.symm.trans ht)
  · change ∀ x : Bool, x = x
    intro x
    rfl

inductive ConstantFunction : ℕ → Type
  | c : ConstantFunction 0
def constantSignature : Signature where
  Sorts := Unit
  Relations := fun _ => Empty
  profile := fun r => r.elim
  Functions := ConstantFunction
  input := fun f => match f with | .c => Fin.elim0
  output := fun _ => ()
@[instance_reducible]
def badConstantModel : OrdinaryModel constantSignature Bool where
  funMap := fun f _ => match f with | .c => true
  RelMap := fun r xs => match r with
    | .sort _ => xs 0 = false
    | .symbol r => r.elim

def constantWitnessBody : Formula constantSignature
    (Fin.snoc (Fin.elim0 : Context constantSignature 0) ()) :=
  .equal (.var 0 rfl) (.app (L := constantSignature) ConstantFunction.c (fun i => Fin.elim0 i))
def constantExists : Sentence constantSignature :=
  .imp (.all () (.imp constantWitnessBody .falsum)) .falsum

theorem sorted_constant_exists (D : Model constantSignature) : D.Models {constantExists} := by
  intro p hp
  have he : p = constantExists := Set.mem_singleton_iff.mp hp
  subst p
  simp [constantExists, constantWitnessBody, Model.Realize, Model.eval,
    Model.assignSnoc, Fin.snoc]
  refine ⟨D.func ConstantFunction.c (fun i => Fin.elim0 i), ?_⟩
  rw [show (0 : Fin 1) = Fin.last 0 from rfl, Fin.lastCases_last]
  apply eq_of_heq
  simp only [Eq.mpr]
  apply heq_of_eq
  congr 1
  funext i
  exact Fin.elim0 i

theorem missing_constant_closure :
    badConstantModel.NonemptySorts ∧ ¬badConstantModel.Closed ∧
    ¬@FirstOrder.Language.Sentence.Realize _ Bool badConstantModel constantExists.erase := by
  refine ⟨?_, ?_, ?_⟩
  · intro s
    exact ⟨false,rfl⟩
  · intro h
    have hc := h ConstantFunction.c Fin.elim0 (fun i => Fin.elim0 i)
    change true = false at hc
    cases hc
  · change ¬¬∀ x : Bool, x = false → (x = true → False)
    intro h
    apply h
    intro x hx
    subst x
    exact Bool.false_ne_true

end Lemmatheca.Entry.ManySortedFunctions
