import Lemmatheca.BethDefinability.BethDefinability

namespace Lemmatheca.Entry.BethDefinability
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.BethDefinability
open Lemmatheca.MathematicalLogic.DefinitionalExtensions
universe u v w
noncomputable section
local instance {M : Type*} : Language.empty.Structure M := Language.emptyStructure

/-- One binary operation, with no equations assumed about it. -/
inductive Operation : ℕ → Type
  | mul : Operation 2

def operationLanguage : Language := ⟨Operation, fun _ => Empty⟩

/-- The actual old-language formula for a two-sided neutral element. -/
def identityFormula : operationLanguage.Formula (Fin 1) :=
  ((BoundedFormula.equal (L := operationLanguage))
      (.func Operation.mul ![.var (.inl 0), .var (.inr 0)]) (.var (.inr 0)) ⊓
    (BoundedFormula.equal (L := operationLanguage))
      (.func Operation.mul ![.var (.inr 0), .var (.inl 0)]) (.var (.inr 0))).all

def someRelated : (extended operationLanguage 1).Sentence :=
  (BoundedFormula.rel (L := extended operationLanguage 1) (Sum.inr AddedRelation.fresh) (fun _ => .var (.inr 0))).ex

def identityMembers : (extended operationLanguage 1).Sentence :=
  close (relationAtom.imp ((oldInclusion (L := operationLanguage) (n := 1)).onFormula
    identityFormula))

def identityTheory : (extended operationLanguage 1).Theory := {someRelated, identityMembers}

private theorem realize_pair {L : Language} {M : Type w} [L.Structure M] {α : Type*}
    (a : α → M) (s t : L.Term α) :
    (fun i : Fin 2 => (![s,t] i).realize a) = ![s.realize a,t.realize a] := by
  funext i
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl <;> rfl

private theorem identityFormula_realize {M : Type w} [operationLanguage.Structure M]
    (a : Fin 1 → M) : identityFormula.Realize a ↔
      ∀ y : M, Structure.funMap (L := operationLanguage) Operation.mul ![a 0,y] = y ∧
        Structure.funMap (L := operationLanguage) Operation.mul ![y,a 0] = y := by
  simp [identityFormula,Formula.Realize,BoundedFormula.Realize,Term.realize,Fin.snoc,realize_pair]

private theorem relationAtom_realize {L : Language} {n : ℕ} {M : Type w}
    [(extended L n).Structure M] (a : Fin n → M) :
    (relationAtom (L := L)).Realize a ↔ Structure.RelMap (L := extended L n) (Sum.inr AddedRelation.fresh) a := by
  rfl

private theorem someRelated_realize {M : Type w} [(extended operationLanguage 1).Structure M] :
    M ⊨ someRelated ↔ ∃ e : M,
      (relationAtom (L := operationLanguage) (n := 1)).Realize (fun _ => e) := by
  simp only [relationAtom_realize]
  simp [someRelated,Sentence.Realize,Formula.Realize,BoundedFormula.realize_ex,
    BoundedFormula.Realize,Term.realize,Fin.snoc]

theorem identity_explicit : DefinedBy identityTheory identityFormula := by
  apply Theory.models_sentence_iff.mpr
  intro M
  let : operationLanguage.Structure M :=
    (oldInclusion (L := operationLanguage) (n := 1)).reduct M
  apply (realize_definingAxiom identityFormula).mpr
  have hm : M ⊨ identityMembers := Theory.realize_sentence_of_mem identityTheory (by simp [identityTheory])
  have hmembers : ∀ a : Fin 1 → M,
      (relationAtom (L := operationLanguage) (n := 1)).Realize a → identityFormula.Realize a := by
    simpa only [identityMembers,realize_close,Formula.realize_imp,LHom.realize_onFormula] using hm
  have hs : M ⊨ someRelated := Theory.realize_sentence_of_mem identityTheory (by simp [identityTheory])
  obtain ⟨e,he⟩ := (someRelated_realize).mp hs
  have heρ := (identityFormula_realize _).mp (hmembers (fun _ => e) he)
  intro a
  refine ⟨hmembers a,?_⟩
  intro ha
  have haρ := (identityFormula_realize a).mp ha
  have hae : a 0 = e := (heρ (a 0)).2.symm.trans (haρ e).1
  have htuple : a = fun _ => e := by
    funext i
    simpa only [Subsingleton.elim i 0] using hae
  rw [htuple]
  exact he

theorem identity_implicit : Implicit identityTheory := by
  exact explicit_implies_implicit ⟨identityFormula,identity_explicit⟩

/-- The full relation is defined by true, uniformly including arity zero. -/
theorem full_relation_definition {L : Language} {n : ℕ} :
    DefinedBy ({close (relationAtom (L := L) (n := n))} : (extended L n).Theory)
      (⊤ : L.Formula (Fin n)) := by
  apply Theory.models_sentence_iff.mpr
  intro M
  let : L.Structure M := (oldInclusion (L := L) (n := n)).reduct M
  apply (realize_definingAxiom (⊤ : L.Formula (Fin n))).mpr
  have hm : M ⊨ close (relationAtom (L := L) (n := n)) :=
    Theory.realize_sentence_of_mem ({close (relationAtom (L := L) (n := n))} : (extended L n).Theory)
      (Set.mem_singleton _)
  intro a
  have ha := (realize_close _).mp hm a
  simpa only [Formula.realize_top,iff_true] using ha

/-- A specified singleton old structure, in the ambient signature universe. -/
@[instance_reducible] def singletonOldStructure (L : Language.{u,v}) :
    L.Structure (ULift.{max u v} Unit) where
  funMap _ _ := ⟨()⟩
  RelMap _ _ := False

/-- The actual singleton and the actual empty/full witnesses used in the answer. -/
theorem singleton_empty_full_models (L : Language.{u,v}) (n : ℕ) :
    letI := singletonOldStructure L
    (letI := expansion (L := L) (fun _ : Fin n → ULift.{max u v} Unit => False)
     ULift.{max u v} Unit ⊨ (∅ : (extended L n).Theory)) ∧
    (letI := expansion (L := L) (fun _ : Fin n → ULift.{max u v} Unit => True)
     ULift.{max u v} Unit ⊨ (∅ : (extended L n).Theory)) ∧
    (fun _ : Fin n → ULift.{max u v} Unit => False) ≠
      (fun _ : Fin n → ULift.{max u v} Unit => True) := by
  let := singletonOldStructure L
  refine ⟨by infer_instance,by infer_instance,?_⟩
  intro heq
  have h := congrFun heq (fun _ => (⟨()⟩ : ULift.{max u v} Unit))
  exact Eq.mp h.symm True.intro

/-- Even with no inputs, the empty and full tuple relations differ. -/
theorem empty_theory_not_implicit (L : Language) (n : ℕ) :
    ¬ Implicit (∅ : (extended L n).Theory) := by
  intro h
  let := singletonOldStructure L
  have hs := singleton_empty_full_models L n
  exact hs.2.2 (h _ _ _ hs.1 hs.2.1)

def allEqual : Language.empty.Sentence :=
  close ((Term.var (0 : Fin 2)).equal (.var 1))

def restrictedFullTheory : (extended Language.empty 1).Theory :=
  {(oldInclusion (L := Language.empty) (n := 1)).onSentence allEqual,
    close (relationAtom (L := Language.empty) (n := 1))}

theorem restricted_full_definition :
    DefinedBy restrictedFullTheory ((Term.var (0 : Fin 1)).equal (.var 0)) := by
  apply Theory.models_sentence_iff.mpr
  intro M
  let : Language.empty.Structure M := (oldInclusion (L := Language.empty) (n := 1)).reduct M
  apply (realize_definingAxiom ((Term.var (0 : Fin 1)).equal (.var 0))).mpr
  have hm : M ⊨ close (relationAtom (L := Language.empty) (n := 1)) :=
    Theory.realize_sentence_of_mem restrictedFullTheory (by simp [restrictedFullTheory])
  intro a
  have ha := (realize_close _).mp hm a
  simpa only [Formula.realize_equal,Term.realize_var,iff_self,iff_true] using ha

theorem restricted_full_implicit : Implicit restrictedFullTheory := by
  exact explicit_implies_implicit ⟨_,restricted_full_definition⟩

/-- A singleton has the unique full-relation expansion satisfying both axioms. -/
theorem singleton_expansion :
    letI := expansion (L := Language.empty) (fun _ : Fin 1 → Unit => True)
    Unit ⊨ restrictedFullTheory := by
  let := expansion (L := Language.empty) (fun _ : Fin 1 → Unit => True)
  constructor
  intro A hA
  simp only [restrictedFullTheory,Set.mem_insert_iff,Set.mem_singleton_iff] at hA
  rcases hA with rfl | rfl
  · rw [LHom.realize_onSentence]
    apply (realize_close _).mpr
    intro a
    change a 0 = a 1
    exact Subsingleton.elim _ _
  · apply (realize_close _).mpr
    intro a
    exact True.intro

/-- The old two-element equality structure has no expansion satisfying the theory. -/
theorem two_element_no_expansion (r : (Fin 1 → Bool) → Prop) :
    letI := expansion (L := Language.empty) r
    ¬ Bool ⊨ restrictedFullTheory := by
  let := expansion (L := Language.empty) r
  change ¬ Bool ⊨ restrictedFullTheory
  intro hm
  have ha : Bool ⊨ (oldInclusion (L := Language.empty) (n := 1)).onSentence allEqual :=
    hm.realize_of_mem _ (by simp [restrictedFullTheory])
  have hold : Bool ⊨ allEqual := by simpa only [LHom.realize_onSentence] using ha
  have heq := (realize_close _).mp hold ![false,true]
  exact Bool.false_ne_true heq

end
end Lemmatheca.Entry.BethDefinability
