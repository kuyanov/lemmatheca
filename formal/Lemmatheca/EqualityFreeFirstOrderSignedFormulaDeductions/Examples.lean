import Lemmatheca.EqualityFreeFirstOrderSignedFormulaDeductions.Public
import Lemmatheca.IntuitionisticFirstOrderDeduction.Examples

namespace Lemmatheca.Entry.EqualityFreeFirstOrderSignedFormulaDeductions
open _root_.FirstOrder _root_.FirstOrder.Language
open Lemmatheca.ProofTheory.ClassicalFirstOrder
open SignedDeductions
universe u v w
variable {L : Language.{u,v}} {α : Type w} {e : Bool}
noncomputable section
local instance signedExamplesFormulaEq {δ : Type w} : DecidableEq (Lemmatheca.ProofTheory.ClassicalFirstOrder.SignedDeductions.Formula L δ) := Classical.decEq _

/-- The older slot names z and the newer slot names w. -/
def nestedFormula (α : Type w) (P : L.Relations 1) (R : L.Relations 2) : Lemmatheca.ProofTheory.ClassicalFirstOrder.SignedDeductions.Formula L α :=
  .neg (.all (.impl (.rel P (fun _ => .var (.inr 0)))
    (.ex (.rel R (fun i => if i = 0 then .var (.inr 0) else .var (.inr 1))))))

def nestedResult (α : Type w) (P : L.Relations 1) (R : L.Relations 2) : Lemmatheca.ProofTheory.ClassicalFirstOrder.SignedDeductions.Formula L α :=
  .ex (.conj (.rel P (fun _ => .var (.inr 0)))
    (.all (.neg (.rel R (fun i => if i = 0 then .var (.inr 0) else .var (.inr 1))))))

theorem nested_equalityFree (α : Type w) (P : L.Relations 1) (R : L.Relations 2) :
    (nestedFormula α P R).EqualityFree := by trivial

theorem nested_reading (α : Type w) (P : L.Relations 1) (R : L.Relations 2) :
    positive (nestedFormula α P R) (nested_equalityFree α P R) = nestedResult α P R := by rfl

def nestedForward {Γ : Context L α} (P : L.Relations 1) (R : L.Relations 2)
    (p : Derivation true e L Γ (nestedFormula α P R)) :
    Derivation true e L Γ (nestedResult α P R) := by
  have q := Raw.toPositive (nestedFormula α P R) (nested_equalityFree α P R) p
  simpa only [nested_reading] using q

def nestedBackward {Γ : Context L α} (P : L.Relations 1) (R : L.Relations 2)
    (p : Derivation true e L Γ (nestedResult α P R)) :
    Derivation true e L Γ (nestedFormula α P R) := by
  apply Raw.fromPositive (nestedFormula α P R) (nested_equalityFree α P R)
  simpa only [nested_reading] using p

def nestedPublicForward {Γ : Context L α} (P : L.Relations 1) (R : L.Relations 2)
    (p : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Proof true e L Γ (nestedFormula α P R)) :
    Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Proof true e L Γ (nestedResult α P R) := by
  have q := Public.toPositive (nestedFormula α P R) (nested_equalityFree α P R) p
  simpa only [nested_reading] using q

def nestedPublicBackward {Γ : Context L α} (P : L.Relations 1) (R : L.Relations 2)
    (p : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Proof true e L Γ (nestedResult α P R)) :
    Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Proof true e L Γ (nestedFormula α P R) := by
  apply Public.fromPositive (nestedFormula α P R) (nested_equalityFree α P R)
  simpa only [nested_reading] using p

theorem signed_dual_reading_ne (L : Language.{u,v}) (α : Type w) :
    (Nnf.and (Nnf.bot : Nnf L α 0) Nnf.bot).dual.read ≠
      Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.neg (Nnf.and (Nnf.bot : Nnf L α 0) Nnf.bot).read := by intro h; cases h

theorem constantFree_equalityFree :
    Lemmatheca.Entry.IntuitionisticFirstOrderDeduction.constantFreeFormula.EqualityFree := by trivial

theorem constantFree_reading :
    positive Lemmatheca.Entry.IntuitionisticFirstOrderDeduction.constantFreeFormula constantFree_equalityFree =
      (.ex (.disj (.neg .falsum) .falsum) : Lemmatheca.ProofTheory.ClassicalFirstOrder.SignedDeductions.Formula Language.empty Empty) := by rfl

def constantFreePositive :
    Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Proof true false Language.empty ∅
      (positive Lemmatheca.Entry.IntuitionisticFirstOrderDeduction.constantFreeFormula constantFree_equalityFree) := by
  exact Public.toPositive _ constantFree_equalityFree
    (Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Proof.classicalize
      Lemmatheca.Entry.IntuitionisticFirstOrderDeduction.constantFreeExistence)

theorem constantFree_raw_impossible (e : Bool) :
    ¬ Nonempty (Derivation true e Language.empty ∅
      (positive Lemmatheca.Entry.IntuitionisticFirstOrderDeduction.constantFreeFormula constantFree_equalityFree)) := by
  rintro ⟨p⟩
  exact Lemmatheca.Entry.IntuitionisticFirstOrderDeduction.constantFreeRawImpossible true e
    ⟨Raw.fromPositive _ constantFree_equalityFree p⟩

end
end Lemmatheca.Entry.EqualityFreeFirstOrderSignedFormulaDeductions
