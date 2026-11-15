import Lemmatheca.BoundedArithmeticNegativeTranslation.Conversions

namespace Lemmatheca.ProofTheory.HeytingArithmetic.BoundedNegativeTranslation
open _root_.FirstOrder _root_.FirstOrder.Language
open Lemmatheca.ProofTheory.FirstOrder.BoundedFormula
open Lemmatheca.ProofTheory.FirstOrder.NegativeTranslation (negative)
open Bounded
noncomputable section
local instance bantUniversalFormulaEq {δ : Type} : DecidableEq (Formula δ) := Classical.decEq _

/-- The actual bounded matrix and the finite native universal prefix are retained. -/
inductive Presentation : Type → Type 1 where
  | bounded {α : Type} (B : Expr α) : Presentation α
  | all {α : Type} (F : Presentation (α ⊕ Unit)) : Presentation α

def Presentation.expand {α : Type} : Presentation α → Formula α
  | .bounded B => B.expand
  | .all F => allUnit F.expand

def Presentation.subst {α β : Type} (F : Presentation α)
    (σ : α → LA.Term β) : Presentation β :=
  match F with
  | .bounded B => .bounded (B.subst σ)
  | .all F => .all (F.subst (unitSubst σ))

def Presentation.rename {α β : Type} (F : Presentation α) (f : α → β) : Presentation β :=
  F.subst (fun x => .var (f x))

/-- A property of the actual shared native formula, witnessed by its presentation. -/
def UniversalBounded {α : Type} (F : Formula α) : Prop :=
  ∃ p : Presentation α, p.expand = F

theorem presentation_expand_subst {α β : Type} (F : Presentation α)
    (σ : α → LA.Term β) : (F.subst σ).expand = F.expand.subst σ := by
  induction F generalizing β with
  | bounded B => exact expand_subst B σ
  | all F ih =>
    simpa only [Presentation.subst, Presentation.expand, allUnit_subst] using
      congrArg allUnit (ih (unitSubst σ))

theorem universal_bounded_subst {α β : Type} (F : Formula α)
    (hF : UniversalBounded F) (σ : α → LA.Term β) :
    UniversalBounded (F.subst σ) := by
  obtain ⟨p, rfl⟩ := hF
  exact ⟨p.subst σ, presentation_expand_subst p σ⟩

private theorem open_presentation {α : Type} (p : Presentation (α ⊕ Unit))
    (D : BF α 1) (h : allUnit p.expand = .all D) : UniversalBounded D.toFormula := by
  have hd : bindUnit p.expand = D := by injection h
  rw [← hd, bindUnit_open]
  exact universal_bounded_subst p.expand ⟨p, rfl⟩
    (fun x => .var (Sum.map id (fun _ => (0 : Fin 1)) x))

theorem universal_bounded_open {α : Type} (D : BF α 1)
    (hD : UniversalBounded (.all D)) : UniversalBounded D.toFormula := by
  obtain ⟨p, hp⟩ := hD
  cases p with
  | all p => exact open_presentation p D hp
  | bounded B =>
    cases B with
    | allLT t B =>
      exact open_presentation
        (.bounded (.impl (.lt (.var (.inr ())) (t.relabel Sum.inl)) B)) D hp
    | allLE t B =>
      exact open_presentation
        (.bounded (.impl (.le (.var (.inr ())) (t.relabel Sum.inl)) B)) D hp
    | _ =>
      simp [Presentation.expand, Expr.expand, termEqual,
        Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.termEqual, Order.leFormula,
        Order.ltFormula, strictExists, inclusiveExists, exUnit] at hp

/-- Family of actual supplied-certificate conversions for the finite prefix. -/
def presentationConversions {α : Type} [Fintype α] (F : Presentation α) :
    Fixed F.expand := by
  cases F with
  | bounded B => exact boundedConversions B
  | all F =>
    simpa only [Presentation.expand, Fixed, NegativeTranslation.negative_allUnit] using
      allUnitConversions (presentationConversions F)

def universalBoundedConversions {α : Type} [Fintype α] (F : Formula α)
    (hF : UniversalBounded F) : Fixed F := by
  let p := Classical.choose hF
  have hp : p.expand = F := Classical.choose_spec hF
  exact hp ▸ presentationConversions p

theorem native_conservation (F : Sentence) (hF : UniversalBounded F) :
    Provable true (∅ : Context Empty) F ↔ Provable false (∅ : Context Empty) F := by
  constructor
  · rintro ⟨p⟩
    exact ⟨(universalBoundedConversions F hF).backward (by
      simpa only [Lemmatheca.ProofTheory.FirstOrder.NegativeTranslation.context,
        Finset.image_empty] using
        NegativeTranslation.interpret p)⟩
  · rintro ⟨p⟩
    exact ⟨p.classicalize⟩

theorem pa_conservation (F : Sentence) (hF : UniversalBounded F) :
    Lemmatheca.MathematicalLogic.FirstOrderProofs.Derives
      Lemmatheca.ModelTheory.ArithmeticTheories.PA F.toClassical ↔
        Provable false (∅ : Context Empty) F := by
  exact (classical_iff_PA F).symm.trans (native_conservation F hF)

end
end Lemmatheca.ProofTheory.HeytingArithmetic.BoundedNegativeTranslation
