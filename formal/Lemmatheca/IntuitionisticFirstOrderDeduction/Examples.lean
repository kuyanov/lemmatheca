import Lemmatheca.IntuitionisticFirstOrderDeduction.Classical
import Lemmatheca.IntuitionisticFirstOrderDeduction.Soundness
import Lemmatheca.IntuitionisticFirstOrderDeduction.EqualityErasure

/-! Explicit deductions and the two counterexamples discussed in the entry. -/
namespace Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction
open _root_.FirstOrder _root_.FirstOrder.Language
universe u v w
variable {L : Language.{u,v}} {α : Type w} {c e : Bool}
noncomputable section
local instance ndExamplesFormulaEq {δ : Type w} : DecidableEq (Formula L δ) :=
  Classical.decEq _

private theorem instantiate_lifted (B : BF L α 1) :
    (B.rename (Sum.inl : α → α ⊕ Fin 1)).instantiate (.var (.inr 0)) = B.toFormula := by
  unfold Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.instantiate Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.instantiateSlots Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.toFormula
  rw [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.map_comp]
  congr 1
  funext x
  cases x with
  | inl x => rfl
  | inr i =>
      have hi : i = 0 := Fin.eq_zero i
      subst i
      rfl


/-- Transport through a universal implication uses an actual existential branch. -/
def Proof.quantifiedTransport (P Q : BF L α 1) :
    Proof false false L ∅ (.impl (.all (.impl P Q)) (.impl (.ex P) (.ex Q))) := by
  apply Proof.impIntro
  apply Proof.impIntro
  let Γ : Context L α := insert (.ex P) (insert (.all (.impl P Q)) ∅)
  apply Proof.exElim (D := P) (C := .ex Q)
    (Proof.assumption (Finset.mem_insert_self _ _))
  let Δ : Context L (α ⊕ Fin 1) := insert P.toFormula (liftContext Γ)
  change Proof false false L Δ ((Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.ex Q).rename Sum.inl)
  have hall : Proof false false L Δ ((Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.all (.impl P Q)).rename Sum.inl) := by
    apply Proof.assumption
    exact Finset.mem_insert_of_mem (Finset.mem_image.mpr
      ⟨.all (.impl P Q), by simp [Γ], rfl⟩)
  have hi := Proof.allElim (c := false) (e := false) (Γ := Δ) (D := (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.impl P Q).rename Sum.inl) (.var (.inr 0))
    (by simpa only [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_all] using hall)
  have hImp : Proof false false L Δ (.impl P.toFormula Q.toFormula) := by
    simpa only [instantiate_lifted,
      Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.toFormula,
      Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.map] using hi
  have hP : Proof false false L Δ P.toFormula := Proof.assumption (Finset.mem_insert_self _ _)
  have hQ := Proof.impElim hImp hP
  have hx := Proof.exIntro (c := false) (e := false) (Γ := Δ) (D := Q.rename Sum.inl) (.var (.inr 0))
    (by simpa only [instantiate_lifted] using hQ)
  simpa only [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_ex] using hx

def Proof.equalSymmetry {Γ : Context L α} {s t : L.Term α}
    (h : Proof c true L Γ (termEqual s t)) : Proof c true L Γ (termEqual t s) := by
  let D : BF L α 1 := .equal (.var (.inr 0)) (s.relabel Sum.inl)
  have inst (r : L.Term α) : D.instantiate r = termEqual r s := by
    simp [D, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.instantiate, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.instantiateSlots, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.map, termEqual,
      Lemmatheca.MathematicalLogic.FirstOrderProofs.term_subst_relabel,
      Lemmatheca.MathematicalLogic.FirstOrderProofs.term_subst_vars]
  have hp := Proof.equalElim D s t h (by simpa only [inst] using Proof.equalIntro (c := c) (Γ := Γ) s)
  simpa only [inst] using hp

def Proof.equalTransitivity {Γ : Context L α} {s t r : L.Term α}
    (hst : Proof c true L Γ (termEqual s t)) (htr : Proof c true L Γ (termEqual t r)) :
    Proof c true L Γ (termEqual s r) := by
  let D : BF L α 1 := .equal (s.relabel Sum.inl) (.var (.inr 0))
  have inst (r : L.Term α) : D.instantiate r = termEqual s r := by
    simp [D, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.instantiate, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.instantiateSlots, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.map, termEqual,
      Lemmatheca.MathematicalLogic.FirstOrderProofs.term_subst_relabel,
      Lemmatheca.MathematicalLogic.FirstOrderProofs.term_subst_vars]
  have hp := Proof.equalElim D t r htr (by simpa only [inst] using hst)
  simpa only [inst] using hp

end
end Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction

namespace Lemmatheca.Entry.IntuitionisticFirstOrderDeduction
open _root_.FirstOrder _root_.FirstOrder.Language
open Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction
noncomputable section
local instance ndCounterexampleFormulaEq {L : Language} {α : Type} :
    DecidableEq (Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Formula L α) := Classical.decEq _

inductive EscapePredicate : ℕ → Type
  | property : EscapePredicate 1

def escapeLanguage : Language := ⟨fun _ => Empty, EscapePredicate⟩

@[instance_reducible]
def escapeStructure : escapeLanguage.Structure Bool where
  funMap := fun s => s.elim
  RelMap := fun R ts => match R with | .property => ts 0 = false

def escapeBody : BF escapeLanguage Unit 1 :=
  .rel EscapePredicate.property (fun _ => .var (.inr 0))

def escapeAtom : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Formula escapeLanguage Unit :=
  .rel EscapePredicate.property (fun _ => .var (.inl ()))

def escapeBranch : Derivation false false escapeLanguage {escapeAtom} escapeAtom :=
  .assumption (Finset.mem_singleton_self _)

/-- The existential premise is true, but its displayed free witness conclusion is false. -/
theorem witness_escape_countermodel :
    letI : escapeLanguage.Structure Bool := escapeStructure
    Holds (.ex escapeBody) (fun _ : Unit => true) ∧
      ¬ Holds escapeAtom (fun _ : Unit => true) := by
  let : escapeLanguage.Structure Bool := escapeStructure
  constructor
  · apply (holds_ex escapeBody _).mpr
    exact ⟨false, rfl⟩
  · change ¬ (true = false)
    decide

theorem witness_escape_not_derivable (c e : Bool) :
    ¬ Derives c e escapeLanguage {(.ex escapeBody)} escapeAtom := by
  let : escapeLanguage.Structure Bool := escapeStructure
  rintro ⟨h⟩
  have hp := h.sound (fun _ : Unit => true) (by
    intro B hB
    rcases Finset.mem_singleton.mp hB with rfl
    exact witness_escape_countermodel.1)
  exact witness_escape_countermodel.2 hp

def constantFreeBody : BF Language.empty Empty 1 := .impl .falsum .falsum
def constantFreeFormula : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Formula Language.empty Empty := .ex constantFreeBody

/-- The actual public proof uses the reserved term indexed by zero. -/
def constantFreeExistence : Proof false false Language.empty ∅ constantFreeFormula := by
  change Derivation false false Language.empty (α := Empty ⊕ ℕ) ∅
    (.ex (.impl .falsum .falsum))
  apply Derivation.exIntro (.var (.inr 0))
  exact .impIntro (.assumption (Finset.mem_insert_self _ _))

/-- Empty-domain raw soundness excludes a raw fixed-parameter proof. -/
theorem constantFreeRawImpossible (c e : Bool) :
    ¬ Nonempty (Derivation c e Language.empty ∅ constantFreeFormula) := by
  let : Language.empty.Structure Empty := Language.emptyStructure
  rintro ⟨h⟩
  have hp := h.sound (Empty.elim : Empty → Empty) (by simp)
  rcases (holds_ex constantFreeBody (Empty.elim : Empty → Empty)).mp hp with ⟨x, _⟩
  exact x.elim

end
end Lemmatheca.Entry.IntuitionisticFirstOrderDeduction
