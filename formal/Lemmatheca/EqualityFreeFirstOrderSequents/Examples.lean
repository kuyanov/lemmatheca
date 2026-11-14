import Lemmatheca.EqualityFreeFirstOrderSequents.Properties

namespace Lemmatheca.Entry.EqualityFreeFirstOrderSequents
open _root_.FirstOrder _root_.FirstOrder.Language
open Lemmatheca.ProofTheory.ClassicalFirstOrder
open Lemmatheca.MathematicalLogic.FirstOrderProofs (term_subst_relabel term_relabel_subst term_subst_vars)
universe u v w
variable {L : Language.{u,v}} {α : Type w}

private theorem lastCases_zero {δ : Sort*} (x : δ) (f : Fin 0 → δ) :
    Fin.lastCases x f (0 : Fin 1) = x := by
  change Fin.lastCases x f (Fin.last 0) = x
  exact Fin.lastCases_last

/-- The actual full universal-instance implication from the worked derivation. -/
def universalInstance (R : L.Relations 1) (t : L.Term α) : EqualityFreeFormula L α :=
  ⟨.impl (.all (.rel R (fun _ => .var (.inr (0 : Fin 1)))))
      (.rel R (fun _ => t.relabel Sum.inl)), ⟨trivial, trivial⟩⟩

noncomputable def universalInstanceProof (R : L.Relations 1) (t : L.Term α) :
    Proof {Nnf.normalize (universalInstance R t).val (universalInstance R t).property true} := by
  let t' : L.Term (α ⊕ ℕ) := t.relabel Sum.inl
  let A : Nnf L (α ⊕ ℕ) 1 := .neg R (fun _ => .var (.inr 0))
  let B : Nnf L (α ⊕ ℕ) 0 := .pos R (fun _ => t'.relabel Sum.inl)
  have p : CoreProof L (insert (A.instantiate t') {B}) :=
    .identity R (fun _ => t'.relabel Sum.inl)
      (by simp [B]) (by simp [A, Nnf.instantiate, Nnf.instantiateSlots, Nnf.map])
  have q : CoreProof L {Nnf.or (Nnf.ex A) B} := by
    simpa only [Finset.insert_empty] using
      (CoreProof.orIntro (Γ := ∅) (A := .ex A) (B := B)
        (by simpa only [Finset.insert_empty] using CoreProof.exIntro A t' p))
  simpa [Proof, renameContext, universalInstance, Nnf.normalize, Nnf.rename,
    Nnf.subst, Nnf.map, A, B, t',
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.freeScope,
    Lemmatheca.ProofTheory.FirstOrder.liftScope, Term.subst,
    term_subst_relabel, term_subst_vars, Term.relabel_relabel,
    lastCases_zero, Function.comp_def] using q

/-- The signed matrix of the closed nonempty-domain excluded-middle example. -/
def excludedMiddleBody (R : L.Relations 1) : Nnf L α 1 :=
  .or (.pos R (fun _ => .var (.inr 0))) (.neg R (fun _ => .var (.inr 0)))

/-- Its witness is the reserved parameter, not a ground term of the language. -/
noncomputable def nonemptyExists (R : L.Relations 1) :
    Proof ({.ex (excludedMiddleBody R)} : Sequent L α) := by
  let t : L.Term (α ⊕ ℕ) := .var (.inr 0)
  let A := excludedMiddleBody (α := α ⊕ ℕ) R
  have p : CoreProof L {Nnf.pos R (fun _ => t.relabel Sum.inl),
      Nnf.neg R (fun _ => t.relabel Sum.inl)} :=
    .identity R (fun _ => t.relabel Sum.inl) (by simp) (by simp)
  have q : CoreProof L {A.instantiate t} := by
    simpa [A, excludedMiddleBody, Nnf.instantiate, Nnf.instantiateSlots, Nnf.map,
      t, Term.relabel] using
      (CoreProof.orIntro (Γ := ∅)
        (A := .pos R (fun _ => t.relabel Sum.inl))
        (B := .neg R (fun _ => t.relabel Sum.inl))
        (by simpa only [Finset.insert_empty] using p))
  have q' : CoreProof L {Nnf.ex A} := by
    simpa only [Finset.insert_empty] using
      (CoreProof.exIntro (Γ := ∅) A t
        (by simpa only [Finset.insert_empty] using q))
  simpa [Proof, renameContext, A, excludedMiddleBody, Nnf.rename, Nnf.subst, Nnf.map,
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.freeScope,
    Lemmatheca.ProofTheory.FirstOrder.liftScope, lastCases_zero] using q' 

inductive UnaryRelation : ℕ → Type
  | r : UnaryRelation 1

def unaryLanguage : Language := ⟨fun _ => Empty, UnaryRelation⟩

/-- No variable or function symbol can start a closed term in this language. -/
theorem noClosedTerm (t : unaryLanguage.Term Empty) : False := by
  cases t with
  | var x => exact x.elim
  | func f _ => exact f.elim

/-- The same valid closed existence has no raw fixed-empty-parameter certificate. -/
theorem noRawExists :
    ¬ Nonempty (CoreProof unaryLanguage
      ({.ex (excludedMiddleBody (α := Empty) UnaryRelation.r)} : Sequent unaryLanguage Empty)) :=
  by
  exact no_raw_existential _ noClosedTerm

/-- The two-element relation is true exactly at the element called zero. -/
@[instance_reducible] def twoElementStructure : unaryLanguage.Structure Bool where
  funMap f _ := f.elim
  RelMap pred ts := match pred with | .r => ts 0 = false

def freshAtom : Nnf unaryLanguage Unit 0 := .pos .r (fun _ => .var (.inl ()))
def freshBody : Nnf unaryLanguage Unit 1 := .pos .r (fun _ => .var (.inr 0))
noncomputable def freshnessPremise : Sequent unaryLanguage Unit := {freshAtom, freshAtom.dual}
noncomputable def freshnessConclusion : Sequent unaryLanguage Unit := {freshAtom.dual, .all freshBody}

noncomputable def freshnessPremiseProof : CoreProof unaryLanguage freshnessPremise := by
  exact .identity .r (fun _ => .var (.inl ()))
    (by simp [freshnessPremise, freshAtom])
    (by simp [freshnessPremise, freshAtom, Nnf.dual])

theorem badEigenparameterCounterexample :
    @SatisfiesSequent unaryLanguage Unit Bool twoElementStructure freshnessPremise (fun _ => false) ∧
    ¬ @SatisfiesSequent unaryLanguage Unit Bool twoElementStructure freshnessConclusion (fun _ => false) :=
  by
  constructor
  · refine ⟨freshAtom, by simp [freshnessPremise], ?_⟩
    change false = false
    rfl
  · rintro ⟨A, hA, ha⟩
    obtain heq | heq := Finset.mem_insert.mp hA
    · subst A
      change ¬ (false = false) at ha
      exact ha rfl
    · have heq' : A = Nnf.all freshBody := Finset.mem_singleton.mp heq
      subst A
      change ∀ x : Bool, _ at ha
      have ht := ha true
      change true = false at ht
      cases ht

end Lemmatheca.Entry.EqualityFreeFirstOrderSequents
