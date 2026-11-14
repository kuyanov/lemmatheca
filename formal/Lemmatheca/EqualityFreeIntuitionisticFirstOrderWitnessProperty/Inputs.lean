import Lemmatheca.EqualityFreeIntuitionisticFirstOrderWitnessProperty.Packets

/-! Supplied cutful/native inputs are normalized by the actual established maps. -/
namespace Lemmatheca.ProofTheory.IntuitionisticFirstOrder.WitnessProperty
open _root_.FirstOrder _root_.FirstOrder.Language
universe u v w
variable {L : Language.{u,v}} {α : Type w}
noncomputable section
local instance ifowpInputsEq {δ : Type w} : DecidableEq (Formula L δ) := Classical.decEq _

def cutDisjunction {A B : Formula L α} (p : RawCutProof L ∅ (.disj A B)) :
    DisjunctPacket A B := rawDisjunction p.eliminate

def cutWitness {B : BF L α 1} (p : RawCutProof L ∅ (.ex B)) : WitnessPacket B := rawWitness p.eliminate

def nativeDisjunction {A B : Formula L α} (hA : A.EqualityFree) (hB : B.EqualityFree)
    (p : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation false false L ∅
      (.disj A B)) : DisjunctPacket A B := rawDisjunction (RawProof.fromNatural p
    (fun C hC => (Finset.notMem_empty C hC).elim) ⟨hA, hB⟩)

def nativeWitness {B : BF L α 1} (hB : B.EqualityFree)
    (p : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation false false L ∅
      (.ex B)) : WitnessPacket B := rawWitness (RawProof.fromNatural p
    (fun C hC => (Finset.notMem_empty C hC).elim) hB)

end
end Lemmatheca.ProofTheory.IntuitionisticFirstOrder.WitnessProperty
