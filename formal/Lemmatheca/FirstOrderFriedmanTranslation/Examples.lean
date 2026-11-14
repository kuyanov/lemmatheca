import Lemmatheca.FirstOrderFriedmanTranslation.Public
import Lemmatheca.IntuitionisticFirstOrderQuantifierPrinciples.Countermodels
import Lemmatheca.IntuitionisticFirstOrderDeduction.Examples

namespace Lemmatheca.Entry.FirstOrderFriedmanTranslation
open _root_.FirstOrder
open Lemmatheca.ProofTheory.FirstOrder
open Lemmatheca.ProofTheory.FirstOrder.FriedmanTranslation
open Lemmatheca.ProofTheory.FirstOrder.QuantifierPrinciples

noncomputable section
local instance friedmanExampleFormulaEq {L : Language} {δ : Type*} :
    DecidableEq (Formula L δ) := Classical.decEq _

/-- P(y), with the single original free name y represented by Unit. -/
def captureParameter : Formula predicateLanguage Unit :=
  .rel UnaryRelation.predicate (fun _ => .var (.inl ()))

/-- P(x), with x in the only available bound slot. -/
def captureBody : BoundedFormula predicateLanguage Unit 1 :=
  .rel UnaryRelation.predicate (fun _ => .var (.inr 0))

def captureSource : Formula predicateLanguage Unit := .all captureBody

def captureCorrect : Formula predicateLanguage Unit :=
  .all (.disj captureBody (protect captureParameter))

def captureNaive : Formula predicateLanguage Unit := .all (.disj captureBody captureBody)

theorem capture_translation : formula captureParameter captureSource = captureCorrect := by
  rfl

/-- The two-element structure P={0}. -/
@[instance_reducible]
def captureStructure : predicateLanguage.Structure (Fin 2) where
  funMap f := f.elim
  RelMap P xs := match P with | .predicate => xs 0 = 0

theorem capture_values :
    letI := captureStructure
    NaturalDeduction.Holds captureCorrect (fun _ => (0 : Fin 2)) ∧
      ¬ NaturalDeduction.Holds captureNaive (fun _ => (0 : Fin 2)) := by
  change (∀ x : Fin 2, x = 0 ∨ (0 : Fin 2) = 0) ∧ ¬ (∀ x : Fin 2, x = 0 ∨ x = 0)
  constructor
  · intro x
    exact Or.inr rfl
  · intro h
    have h1 := h 1
    exact (by decide : ¬ ((1 : Fin 2) = 0 ∨ (1 : Fin 2) = 0)) h1

def termlessParameter : Formula Language.empty Empty := .impl .falsum .falsum

def termlessSource : Formula Language.empty Empty := .ex .falsum

/-- Falsum elimination can produce this existential without choosing a term. -/
def termlessSourceProof :
    NaturalDeduction.Derivation false false Language.empty {.falsum} termlessSource :=
  .falsumElim (.assumption (Finset.mem_singleton_self _))

theorem termless_no_term : ¬ Nonempty (Language.empty.Term Empty) := by
  rintro ⟨t⟩
  cases t with
  | var x => exact x.elim
  | func f _ => exact f.elim

theorem termless_endpoints :
    context termlessParameter ({.falsum} : NaturalDeduction.Context Language.empty Empty) =
        {termlessParameter} ∧
      formula termlessParameter termlessSource =
        IntuitionisticFirstOrderDeduction.constantFreeFormula := by
  constructor
  · simp only [context, Finset.image_singleton, formula]
  · rfl

theorem termless_raw_impossible :
    ¬ Nonempty (NaturalDeduction.Derivation false false Language.empty {termlessParameter}
      (formula termlessParameter termlessSource)) := by
  let : Language.empty.Structure Empty := Language.emptyStructure
  rintro ⟨p⟩
  have hp := p.sound (Empty.elim : Empty → Empty) (by
    intro D hD
    have hD' : D = termlessParameter := Finset.mem_singleton.mp hD
    subst D
    exact fun h => h)
  rw [termless_endpoints.2] at hp
  rcases (NaturalDeduction.holds_ex IntuitionisticFirstOrderDeduction.constantFreeBody
    (Empty.elim : Empty → Empty)).mp hp with ⟨x, _⟩
  exact x.elim

/-- Translate the actual reserved rename of the termless raw source tree. -/
def termlessPublicTranslation :
    NaturalDeduction.Proof false false Language.empty
      (context termlessParameter {.falsum}) (formula termlessParameter termlessSource) :=
  translatePublic termlessParameter (termlessSourceProof.rename (Sum.inl : Empty → Empty ⊕ ℕ))

end
end Lemmatheca.Entry.FirstOrderFriedmanTranslation
