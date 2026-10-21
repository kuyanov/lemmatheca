import Lemmatheca.FirstOrderProofs.FirstOrderProofs

/-! The two-element countermodel to unrestricted witness generalization. -/
namespace Lemmatheca.Entry.FirstOrderProofs
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.FirstOrderProofs

inductive ConstantSymbol : ℕ → Type
  | name : ConstantSymbol 0
inductive PredicateSymbol : ℕ → Type
  | property : PredicateSymbol 1

def witnessLanguage : Language := ⟨ConstantSymbol, PredicateSymbol⟩
@[instance_reducible]
def witnessStructure : witnessLanguage.Structure Bool where
  funMap := fun s _ => match s with | .name => false
  RelMap := fun s ts => match s with | .property => ts 0 = true

def witnessBody : witnessLanguage.BoundedFormula Empty 1 := unaryBody .property

def namedProperty : witnessLanguage.Sentence :=
  Relations.formula₁ (L := witnessLanguage) PredicateSymbol.property
    (Constants.term (L := witnessLanguage) ConstantSymbol.name)

theorem witness_countermodel :
    @Sentence.Realize witnessLanguage Bool witnessStructure witnessBody.ex ∧
    ¬ @Sentence.Realize witnessLanguage Bool witnessStructure witnessBody.all ∧
    ¬ @Sentence.Realize witnessLanguage Bool witnessStructure namedProperty := by
  let : witnessLanguage.Structure Bool := witnessStructure
  constructor
  · apply BoundedFormula.realize_ex.mpr
    exact ⟨true, rfl⟩
  · constructor
    · intro h
      exact Bool.false_ne_true (h false)
    · intro h
      exact Bool.false_ne_true h

theorem witness_not_universal : ¬ Derives ({witnessBody.ex} : witnessLanguage.Theory)
    witnessBody.all := by
  let : witnessLanguage.Structure Bool := witnessStructure
  intro h
  have hp := derives_sound h (default : Empty → Bool) (by
    intro A hA
    rcases Set.mem_singleton_iff.mp hA with rfl
    exact witness_countermodel.1)
  exact witness_countermodel.2.1 hp

theorem witness_not_named : ¬ Derives ({witnessBody.ex} : witnessLanguage.Theory)
    namedProperty := by
  let : witnessLanguage.Structure Bool := witnessStructure
  intro h
  have hp := derives_sound h (default : Empty → Bool) (by
    intro A hA
    rcases Set.mem_singleton_iff.mp hA with rfl
    exact witness_countermodel.1)
  exact witness_countermodel.2.2 hp

end Lemmatheca.Entry.FirstOrderProofs
