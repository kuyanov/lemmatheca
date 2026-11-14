import Lemmatheca.HeytingArithmeticAddition.Instances
import Lemmatheca.HeytingArithmeticAddition.Finiteness
import Lemmatheca.IntuitionisticFirstOrderDeduction.Soundness

namespace Lemmatheca.Entry.HeytingArithmeticAddition
open _root_.FirstOrder _root_.FirstOrder.Language
open Lemmatheca.ProofTheory.HeytingArithmetic
open Lemmatheca.ProofTheory.HeytingArithmetic.Addition
universe u
variable {α : Type u}
noncomputable section
local instance haAdditionExamplesEq {β : Type*} : DecidableEq (Formula β) := Classical.decEq _

/-- The original shared addend is the displayed term, rather than a computed numeral. -/
def workedCancellation {Γ : Context α} (x y : LA.Term α)
    (p : Certificate false Γ
      (termEqual (addTerm (addTerm x ((numeral 2).relabel Empty.elim)) y)
        (addTerm (addTerm x ((numeral 2).relabel Empty.elim)) ((numeral 3).relabel Empty.elim)))) :
    Certificate false Γ (termEqual y ((numeral 3).relabel Empty.elim)) :=
  cancelLeft (addTerm x ((numeral 2).relabel Empty.elim)) y
    ((numeral 3).relabel Empty.elim) p

/-- This interprets the actual arithmetic symbols, with no arithmetic axioms assumed. -/
@[instance_reducible]
def collapsingStructure : LA.Structure Bool where
  funMap := fun f ts => match f with
    | .zero => false
    | .succ => ts 0
    | .add => false
    | .mul => false
  RelMap := fun r => r.elim

theorem collapsing_not_cancel :
    letI : LA.Structure Bool := collapsingStructure
    ¬ Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Holds (M := Bool)
      cancelLeftSentence Empty.elim := by
  change ¬ (∀ x y z : Bool, (false : Bool) = false → y = z)
  decide

theorem cancellation_not_logical :
    ¬ Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derives false true LA
      (∅ : Context Empty) cancelLeftSentence := by
  let : LA.Structure Bool := collapsingStructure
  rintro ⟨p⟩
  exact collapsing_not_cancel (p.sound Empty.elim (by simp))

end
end Lemmatheca.Entry.HeytingArithmeticAddition
