import Lemmatheca.EqualityFreeIntuitionisticFirstOrderHarropExtraction.Extraction
import Lemmatheca.EqualityFreeIntuitionisticFirstOrderCutElimination.Properties

/-! The raw cut and native wrappers act on the specified normalized input. -/
namespace Lemmatheca.ProofTheory.IntuitionisticFirstOrder.EqualityFreeHarrop
open _root_.FirstOrder _root_.FirstOrder.Language
universe u v w
variable {L : Language.{u,v}} {α : Type w}
noncomputable section
local instance ifohInputsEq {δ : Type w} : DecidableEq (Formula L δ) := Classical.decEq _

def cutDisjunction {Γ : Context L α} {A B : Formula L α} (hΓ : ContextHarrop Γ)
    (p : RawCutProof L Γ (.disj A B)) : DisjunctPacket Γ A B :=
  disjunction hΓ p.eliminate

def cutOutcome {Γ : Context L α} {B : BF L α 1} (hΓ : ContextHarrop Γ)
    (p : RawCutProof L Γ (.ex B)) : Outcome Γ B := outcome hΓ p.eliminate

def cutWitnessOfConsistent {Γ : Context L α} {B : BF L α 1}
    (hΓ : ContextHarrop Γ) (hCon : Consistent Γ) (p : RawCutProof L Γ (.ex B)) :
    WitnessPacket Γ B := witnessOfConsistent hΓ hCon p.eliminate

def cutWitnessWithDefault {Γ : Context L α} {B : BF L α 1}
    (hΓ : ContextHarrop Γ) (r : L.Term α) (p : RawCutProof L Γ (.ex B)) :
    WitnessPacket Γ B := witnessWithDefault hΓ r p.eliminate

def nativeDisjunction {Γ : Context L α} {A B : Formula L α} (hΓ : ContextHarrop Γ)
    (hA : A.EqualityFree) (hB : B.EqualityFree)
    (p : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation false false L Γ (.disj A B)) :
    DisjunctPacket Γ A B :=
  disjunction hΓ (RawProof.fromNatural p (context_pure hΓ) ⟨hA, hB⟩)

def nativeOutcome {Γ : Context L α} {B : BF L α 1} (hΓ : ContextHarrop Γ)
    (hB : B.EqualityFree)
    (p : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation false false L Γ (.ex B)) :
    Outcome Γ B := outcome hΓ (RawProof.fromNatural p (context_pure hΓ) hB)

def nativeWitnessOfConsistent {Γ : Context L α} {B : BF L α 1}
    (hΓ : ContextHarrop Γ) (hCon : Consistent Γ) (hB : B.EqualityFree)
    (p : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation false false L Γ (.ex B)) :
    WitnessPacket Γ B :=
  witnessOfConsistent hΓ hCon (RawProof.fromNatural p (context_pure hΓ) hB)

def nativeWitnessWithDefault {Γ : Context L α} {B : BF L α 1}
    (hΓ : ContextHarrop Γ) (r : L.Term α) (hB : B.EqualityFree)
    (p : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation false false L Γ (.ex B)) :
    WitnessPacket Γ B :=
  witnessWithDefault hΓ r (RawProof.fromNatural p (context_pure hΓ) hB)

end
end Lemmatheca.ProofTheory.IntuitionisticFirstOrder.EqualityFreeHarrop
