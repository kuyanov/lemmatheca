import Lemmatheca.EqualityFreeFirstOrderSequentSubstitution.Transformations

namespace Lemmatheca.Entry.EqualityFreeFirstOrderSequentSubstitution
open _root_.FirstOrder _root_.FirstOrder.Language
open Lemmatheca.ProofTheory.ClassicalFirstOrder
open Lemmatheca.MathematicalLogic.FirstOrderProofs (liftSubst)
universe u v
noncomputable section

variable {L : Language.{u,v}}

def exampleBody (R : L.Relations 2) : Nnf L Unit 1 :=
  .pos R (fun i => if i = 0 then .var (.inl ()) else .var (.inr 0))

def exampleContext (R : L.Relations 2) : Sequent L Unit :=
  {(.all (exampleBody R)), (.ex (exampleBody R).dual)}

private def castExample {α : Type} {Γ Δ : Sequent L α} (h : Γ = Δ)
    (p : CoreProof L Γ) : CoreProof L Δ := h ▸ p

@[simp] private theorem height_castExample {α : Type} {Γ Δ : Sequent L α} (h : Γ = Δ)
    (p : CoreProof L Γ) : (castExample h p).height = p.height := by
  subst Δ
  rfl

private def exampleWithHeight (R : L.Relations 2) :
    {p : CoreProof L (exampleContext R) // p.height = 2} := by
  let A := exampleBody R
  let ts : Fin 2 → L.Term ((Unit ⊕ Fin 1) ⊕ Fin 0) := fun i =>
    ((if i = 0 then .var (.inl ()) else .var (.inr 0)) : L.Term (Unit ⊕ Fin 1)).subst
      (fun x => .var (.inl x))
  let p : CoreProof L (insert A.dual.toFormula {A.toFormula}) :=
    .identity R ts (by simp [A, exampleBody, Nnf.toFormula, Nnf.map, ts])
      (by simp [A, exampleBody, Nnf.toFormula, Nnf.map, Nnf.dual, ts])
  have hinst : (A.dual.rename (Sum.inl : Unit → Unit ⊕ Fin 1)).instantiate (.var (.inr 0)) =
      A.dual.toFormula := Nnf.instantiate_rename_fresh A.dual
  let q := castExample (congrArg (fun F => insert F {A.toFormula}) hinst.symm) p
  let ex : CoreProof L (insert (.ex (A.dual.rename (Sum.inl : Unit → Unit ⊕ Fin 1)))
      {A.toFormula}) := .exIntro _ (.var (.inr 0)) q
  have hc : insert (.ex (A.dual.rename (Sum.inl : Unit → Unit ⊕ Fin 1))) {A.toFormula} =
      insert A.toFormula (liftContext ({.ex A.dual} : Sequent L Unit)) := by
    simp only [liftContext, renameContext, Finset.image_singleton, Nnf.rename,
      Nnf.subst_ex]
    exact Finset.pair_comm _ _
  refine ⟨.allIntro A (castExample hc ex), ?_⟩
  change (castExample hc ex).height + 1 = 2
  rw [height_castExample]
  change q.height + 1 + 1 = 2
  rw [height_castExample]
  rfl

/-- The explicit universal/existential/identity tree from the worked example. -/
def exampleProof (R : L.Relations 2) : CoreProof L (exampleContext R) := by
  exact (exampleWithHeight R).val

theorem exampleProof_height (R : L.Relations 2) : (exampleProof R).height = 2 := by
  exact (exampleWithHeight R).property

def exampleSubstitution (f : L.Functions 1) : Unit → L.Term Unit :=
  fun _ => .func f (fun _ => .var ())

def substitutedExample (R : L.Relations 2) (f : L.Functions 1) :
    CoreProof L (substContext (exampleContext R) (exampleSubstitution f)) :=
  (exampleProof R).substitute (exampleSubstitution f)

theorem substitutedExample_body (R : L.Relations 2) (f : L.Functions 1) :
    (exampleBody R).subst (exampleSubstitution f) =
      .pos R (fun i => if i = 0 then
        .func f (fun _ => .var (.inl ())) else .var (.inr 0)) := by
  unfold exampleBody Nnf.subst Nnf.map
  congr 1
  funext i
  by_cases hi : i = 0 <;>
    simp [hi, exampleSubstitution, Term.subst, Term.relabel,
      Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.freeScope]

theorem substitutedExample_context (R : L.Relations 2) (f : L.Functions 1) :
    substContext (exampleContext R) (exampleSubstitution f) =
      {(.all ((exampleBody R).subst (exampleSubstitution f))),
        (.ex ((exampleBody R).subst (exampleSubstitution f)).dual)} := by
  simp only [exampleContext, substContext, Finset.image_insert, Finset.image_singleton,
    Nnf.subst_all, Nnf.subst_ex, Nnf.dual_subst]

theorem substitutedExample_height (R : L.Relations 2) (f : L.Functions 1) :
    (substitutedExample R f).height = 2 := by
  simp only [substitutedExample, CoreProof.height_substitute, exampleProof_height]

inductive BinaryPredicate : ℕ → Type
  | relation : BinaryPredicate 2

def captureLanguage : Language := ⟨fun _ => Empty, BinaryPredicate⟩

@[instance_reducible] def captureStructure : captureLanguage.Structure Bool where
  funMap := fun s => s.elim
  RelMap := fun R ts => match R with | .relation => ts 0 = ts 1

/-- Correct free-variable replacement keeps the second argument bound and the first free. -/
def correctCaptureBody : Nnf captureLanguage Unit 1 := exampleBody BinaryPredicate.relation

def capturedBody : Nnf captureLanguage Unit 1 :=
  .pos BinaryPredicate.relation (fun _ => .var (.inr 0))

theorem capture_countermodel :
    letI : captureLanguage.Structure Bool := captureStructure
    ¬ (correctCaptureBody.all.rename (id : Unit → Unit)).Realize (fun _ => false) ∧
      capturedBody.all.Realize (fun _ : Unit => false) := by
  change (¬ ∀ b : Bool, false = b) ∧ (∀ b : Bool, b = b)
  constructor
  · intro h
    have hf := h true
    cases hf
  · intro b
    rfl

/-- Both old names have the same variable image. -/
def collapsedSubstitution : Bool → captureLanguage.Term Unit := fun _ => .var ()

theorem collapsed_protected_images :
    liftSubst collapsedSubstitution 1 (.inl false) = .var (.inl ()) ∧
    liftSubst collapsedSubstitution 1 (.inl true) = .var (.inl ()) ∧
    liftSubst collapsedSubstitution 1 (.inr 0) = .var (.inr 0) ∧
    (liftSubst collapsedSubstitution 1 (.inl false) ≠
      liftSubst collapsedSubstitution 1 (.inr 0)) := by
  simp [liftSubst, collapsedSubstitution]

end
end Lemmatheca.Entry.EqualityFreeFirstOrderSequentSubstitution
