import Lemmatheca.EqualityFreeIntuitionisticFirstOrderCutElimination.Subformulas
import Lemmatheca.IntuitionisticFirstOrderDeduction.Examples

namespace Lemmatheca.Entry.EqualityFreeIntuitionisticFirstOrderCutElimination
open _root_.FirstOrder _root_.FirstOrder.Language
open Lemmatheca.ProofTheory.IntuitionisticFirstOrder
universe u v w
variable {L : Language.{u,v}} {α : Type w}
noncomputable section
local instance ifocutExamplesFormulaEq {K : Language.{u,v}} {δ : Type w} :
    DecidableEq (Lemmatheca.ProofTheory.IntuitionisticFirstOrder.Formula K δ) := Classical.decEq _

/-- The actual consumer for an ordinary universal instantiation. -/
def universalUse (B : BF L α 1) (hB : B.EqualityFree) (t : L.Term α) :
    CoreProof L {Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.all B} (B.instantiate t) := by
  apply CoreProof.allLeft t (Finset.mem_singleton_self _)
  exact CoreProof.identity _
    ((Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.equalityFree_map B _).mpr hB)
    (Finset.mem_insert_self _ _)

/-- An open existential sequent has its specified cut-free identity tree. -/
def openExistential :
    RawProof Lemmatheca.Entry.IntuitionisticFirstOrderDeduction.escapeLanguage
      {Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.ex Lemmatheca.Entry.IntuitionisticFirstOrderDeduction.escapeBody}
      (.ex Lemmatheca.Entry.IntuitionisticFirstOrderDeduction.escapeBody) := by
  refine ⟨CoreProof.identity _ True.intro (Finset.mem_singleton_self _), ?_, True.intro⟩
  intro A hA
  rcases Finset.mem_singleton.mp hA with rfl
  exact True.intro

theorem no_raw_prescribed_instance :
    ¬ Nonempty (CutProof Lemmatheca.Entry.IntuitionisticFirstOrderDeduction.escapeLanguage
      {Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.ex Lemmatheca.Entry.IntuitionisticFirstOrderDeduction.escapeBody}
      Lemmatheca.Entry.IntuitionisticFirstOrderDeduction.escapeAtom) := by
  let : Lemmatheca.Entry.IntuitionisticFirstOrderDeduction.escapeLanguage.Structure Bool :=
    Lemmatheca.Entry.IntuitionisticFirstOrderDeduction.escapeStructure
  rintro ⟨p⟩
  have h := p.toNatural.sound (fun _ : Unit => true) (by
    intro A hA
    rcases Finset.mem_singleton.mp hA with rfl
    exact Lemmatheca.Entry.IntuitionisticFirstOrderDeduction.witness_escape_countermodel.1)
  exact Lemmatheca.Entry.IntuitionisticFirstOrderDeduction.witness_escape_countermodel.2 h

theorem no_public_prescribed_instance :
    ¬ CutDerives Lemmatheca.Entry.IntuitionisticFirstOrderDeduction.escapeLanguage
      {Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.ex Lemmatheca.Entry.IntuitionisticFirstOrderDeduction.escapeBody}
      Lemmatheca.Entry.IntuitionisticFirstOrderDeduction.escapeAtom := by
  rintro ⟨p⟩
  exact Lemmatheca.Entry.IntuitionisticFirstOrderDeduction.witness_escape_not_derivable false false
    ⟨p.toNatural⟩

end
end Lemmatheca.Entry.EqualityFreeIntuitionisticFirstOrderCutElimination
