import Lemmatheca.IntuitionisticFirstOrderQuantifierPrinciples.Countermodels
import Mathlib.Tactic.NormNum

namespace Lemmatheca.Entry.IntuitionisticFirstOrderQuantifierPrinciples
open _root_.FirstOrder _root_.FirstOrder.Language
open Lemmatheca.ProofTheory.FirstOrder
open Lemmatheca.ProofTheory.FirstOrder.Kripke
open Lemmatheca.ProofTheory.FirstOrder.QuantifierPrinciples
noncomputable section
set_option maxHeartbeats 1200000
open Lemmatheca.Entry.IntuitionisticFirstOrderKripkeSemantics

/-- The specified two-element, one-world structure separates the distributions. -/
def splitModel : Model Lemmatheca.Entry.IntuitionisticFirstOrderKripkeSemantics.growingLanguage PUnit :=
  @singleton Lemmatheca.Entry.IntuitionisticFirstOrderKripkeSemantics.growingLanguage (Fin 2) (Lemmatheca.Entry.IntuitionisticFirstOrderKripkeSemantics.growingStructure 1) inferInstance

def exConjunctionConverse : Lemmatheca.ProofTheory.FirstOrder.Formula Lemmatheca.Entry.IntuitionisticFirstOrderKripkeSemantics.growingLanguage Empty :=
  .impl (.conj (.ex Lemmatheca.Entry.IntuitionisticFirstOrderKripkeSemantics.presentBody) (.ex Lemmatheca.Entry.IntuitionisticFirstOrderKripkeSemantics.newBody))
    (.ex (.conj Lemmatheca.Entry.IntuitionisticFirstOrderKripkeSemantics.presentBody Lemmatheca.Entry.IntuitionisticFirstOrderKripkeSemantics.newBody))

def allDisjunctionConverse : Lemmatheca.ProofTheory.FirstOrder.Formula Lemmatheca.Entry.IntuitionisticFirstOrderKripkeSemantics.growingLanguage Empty :=
  .impl (.all (.disj Lemmatheca.Entry.IntuitionisticFirstOrderKripkeSemantics.presentBody Lemmatheca.Entry.IntuitionisticFirstOrderKripkeSemantics.newBody))
    (.disj (.all Lemmatheca.Entry.IntuitionisticFirstOrderKripkeSemantics.presentBody) (.all Lemmatheca.Entry.IntuitionisticFirstOrderKripkeSemantics.newBody))

local instance splitStructure : growingLanguage.Structure (Fin 2) := growingStructure 1

private theorem split_forcing {x : PUnit.{u+1}}
    (A : Lemmatheca.ProofTheory.FirstOrder.Formula growingLanguage Empty) :
    Holds splitModel x A Empty.elim ↔ A.realize (Sum.elim Empty.elim Fin.elim0 : Empty ⊕ Fin 0 → Fin 2) :=
  singleton_forcing (Fin 2) A x _

theorem splitModel_values :
    Holds splitModel PUnit.unit (.conj (.ex Lemmatheca.Entry.IntuitionisticFirstOrderKripkeSemantics.presentBody) (.ex Lemmatheca.Entry.IntuitionisticFirstOrderKripkeSemantics.newBody)) Empty.elim ∧
    ¬ Holds splitModel PUnit.unit (.ex (.conj Lemmatheca.Entry.IntuitionisticFirstOrderKripkeSemantics.presentBody Lemmatheca.Entry.IntuitionisticFirstOrderKripkeSemantics.newBody)) Empty.elim ∧
    Holds splitModel PUnit.unit (.all (.disj Lemmatheca.Entry.IntuitionisticFirstOrderKripkeSemantics.presentBody Lemmatheca.Entry.IntuitionisticFirstOrderKripkeSemantics.newBody)) Empty.elim ∧
    ¬ Holds splitModel PUnit.unit (.disj (.all Lemmatheca.Entry.IntuitionisticFirstOrderKripkeSemantics.presentBody) (.all Lemmatheca.Entry.IntuitionisticFirstOrderKripkeSemantics.newBody)) Empty.elim := by
  simp only [split_forcing]
  change ((∃ x : Fin 2, x.val = 0) ∧ (∃ x : Fin 2, x.val = 1)) ∧
    (¬ ∃ x : Fin 2, x.val = 0 ∧ x.val = 1) ∧
    (∀ x : Fin 2, x.val = 0 ∨ x.val = 1) ∧
    ¬ ((∀ x : Fin 2, x.val = 0) ∨ (∀ x : Fin 2, x.val = 1))
  refine ⟨⟨⟨0, rfl⟩, ⟨1, rfl⟩⟩, ?_, ?_, ?_⟩
  · rintro ⟨x, h0, h1⟩
    omega
  · intro x
    fin_cases x <;> simp
  · rintro (h | h)
    · have hp := h 1
      norm_num at hp
    · have hp := h 0
      norm_num at hp

theorem splitModel_converse_failures :
    (¬ Holds splitModel PUnit.unit exConjunctionConverse Empty.elim) ∧
    (¬ Holds splitModel PUnit.unit allDisjunctionConverse Empty.elim) := by
  constructor
  · rw [split_forcing]
    change ¬ (((∃ x : Fin 2, x.val = 0) ∧ (∃ x : Fin 2, x.val = 1)) →
      ∃ x : Fin 2, x.val = 0 ∧ x.val = 1)
    intro h
    obtain ⟨x, h0, h1⟩ := h ⟨⟨0, rfl⟩, ⟨1, rfl⟩⟩
    omega
  · rw [split_forcing]
    change ¬ ((∀ x : Fin 2, x.val = 0 ∨ x.val = 1) →
      (∀ x : Fin 2, x.val = 0) ∨ (∀ x : Fin 2, x.val = 1))
    intro h
    have hh : ∀ x : Fin 2, x.val = 0 ∨ x.val = 1 := by
      intro x
      fin_cases x <;> simp
    rcases h hh with h0 | h1
    · have hp := h0 1
      norm_num at hp
    · have hp := h1 0
      norm_num at hp

theorem distribution_converses_nonderivable (e : Bool) :
    (¬ NaturalDeduction.Derives false e Lemmatheca.Entry.IntuitionisticFirstOrderKripkeSemantics.growingLanguage ∅ exConjunctionConverse) ∧
    (¬ NaturalDeduction.Derives false e Lemmatheca.Entry.IntuitionisticFirstOrderKripkeSemantics.growingLanguage ∅ allDisjunctionConverse) := by
  constructor
  · rintro ⟨p⟩
    exact splitModel_converse_failures.{0, 0}.1 (proof_sound splitModel.{0} p PUnit.unit Empty.elim (by simp))
  · rintro ⟨p⟩
    exact splitModel_converse_failures.{0, 0}.2 (proof_sound splitModel.{0} p PUnit.unit Empty.elim (by simp))

/-- Nonempty one-point structures interpreting every relation as true. -/
@[instance_reducible]
def allTrueStructure (L : Language) : L.Structure PUnit where
  funMap _ _ := PUnit.unit
  RelMap _ _ := True

def allTrueModel (L : Language) : Model L PUnit :=
  @singleton L PUnit (allTrueStructure L) inferInstance

theorem allTrue_CD : Holds (allTrueModel Lemmatheca.Entry.IntuitionisticFirstOrderKripkeSemantics.growingLanguage) PUnit.unit growingCD Empty.elim := by
  let := allTrueStructure growingLanguage
  apply (singleton_forcing _ growingCD _ _).mpr
  change ((∀ x : PUnit, (∃ y : PUnit, True) ∨ True) →
    (∃ y : PUnit, True) ∨ (∀ x : PUnit, True))
  intro _
  exact Or.inl ⟨PUnit.unit, trivial⟩

theorem allTrue_DNS : Holds (allTrueModel predicateLanguage) PUnit.unit doubleNegationShift Empty.elim := by
  let := allTrueStructure predicateLanguage
  apply (singleton_forcing _ doubleNegationShift _ _).mpr
  change (∀ x : PUnit, ¬¬True) → ¬¬(∀ x : PUnit, True)
  intro _ hn
  exact hn (fun _ => trivial)

theorem allTrue_doubleNeg_G :
    Holds (allTrueModel predicateLanguage) PUnit.unit (.neg (.neg allExcludedMiddle)) Empty.elim := by
  let := allTrueStructure predicateLanguage
  apply (singleton_forcing _ (.neg (.neg allExcludedMiddle)) _ _).mpr
  change ¬¬ (∀ x : PUnit, True ∨ ¬True)
  intro hn
  exact hn (fun _ => Or.inl trivial)

theorem principle_negations_nonderivable (e : Bool) :
    (¬ NaturalDeduction.Derives false e Lemmatheca.Entry.IntuitionisticFirstOrderKripkeSemantics.growingLanguage ∅ (.neg growingCD)) ∧
    (¬ NaturalDeduction.Derives false e predicateLanguage ∅ (.neg doubleNegationShift)) ∧
    (¬ NaturalDeduction.Derives false e predicateLanguage ∅ (.neg (.neg (.neg allExcludedMiddle)))) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨p⟩
    have hp := (proof_sound (allTrueModel.{0, 0, 0, 0} growingLanguage) p PUnit.unit Empty.elim (by simp))
      PUnit.unit le_rfl
    rw [transport_refl] at hp
    exact hp allTrue_CD.{0, 0}
  · rintro ⟨p⟩
    have hp := (proof_sound (allTrueModel.{0, 0, 0, 0} predicateLanguage) p PUnit.unit Empty.elim (by simp))
      PUnit.unit le_rfl
    rw [transport_refl] at hp
    exact hp allTrue_DNS.{0, 0}
  · rintro ⟨p⟩
    have hp := (proof_sound (allTrueModel.{0, 0, 0, 0} predicateLanguage) p PUnit.unit Empty.elim (by simp))
      PUnit.unit le_rfl
    rw [transport_refl] at hp
    exact hp allTrue_doubleNeg_G.{0, 0}

end
end Lemmatheca.Entry.IntuitionisticFirstOrderQuantifierPrinciples
