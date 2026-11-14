import Lemmatheca.EqualityFreeIntuitionisticFirstOrderHarropExtraction.Syntax
import Lemmatheca.EqualityFreeIntuitionisticFirstOrderSequents.Structural

/-! Every packet stores actual raw certificates in its stated allowed context. -/
namespace Lemmatheca.ProofTheory.IntuitionisticFirstOrder.EqualityFreeHarrop
open _root_.FirstOrder _root_.FirstOrder.Language
universe u v w
variable {L : Language.{u,v}} {α : Type w}
noncomputable section
local instance ifohPacketsEq {δ : Type w} : DecidableEq (Formula L δ) := Classical.decEq _

abbrev DisjunctPacket (Γ : Context L α) (A B : Formula L α) :=
  Sum (RawProof L Γ A) (RawProof L Γ B)

structure WitnessPacket (Γ : Context L α) (B : BF L α 1) : Type max u v (w+1) where
  term : L.Term α
  proof : RawProof L Γ (B.instantiate term)

abbrev Outcome (Γ : Context L α) (B : BF L α 1) :=
  Sum (WitnessPacket Γ B) (RawProof L Γ .falsum)

def mapDisjunct {Γ Δ : Context L α} {A B : Formula L α}
    (f : ∀ C : Formula L α, RawProof L Γ C → RawProof L Δ C)
    (d : DisjunctPacket Γ A B) : DisjunctPacket Δ A B :=
  Sum.map (f A) (f B) d

def mapWitness {Γ Δ : Context L α} {B : BF L α 1}
    (f : ∀ C : Formula L α, RawProof L Γ C → RawProof L Δ C)
    (d : WitnessPacket Γ B) : WitnessPacket Δ B := ⟨d.term, f _ d.proof⟩

def mapOutcome {Γ Δ : Context L α} {B : BF L α 1}
    (f : ∀ C : Formula L α, RawProof L Γ C → RawProof L Δ C)
    (d : Outcome Γ B) : Outcome Δ B :=
  Sum.map (mapWitness f) (f .falsum) d

/-- The supplied principal and continuation tree occur literally in the output. -/
def conjunctionLift {Γ : Context L α} {C D A : Formula L α}
    (h : .conj C D ∈ Γ) (q : RawProof L (insert C (insert D Γ)) A) : RawProof L Γ A :=
  ⟨.conjLeft h q.tree,
    (fun E hE => q.context_pure E (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hE))),
    q.conclusion_pure⟩

def implicationLift {Γ : Context L α} {C D A : Formula L α}
    (h : .impl C D ∈ Γ) (antecedent : RawProof L Γ C)
    (q : RawProof L (insert D Γ) A) : RawProof L Γ A :=
  ⟨.implLeft h antecedent.tree q.tree, antecedent.context_pure, q.conclusion_pure⟩

def universalLift {Γ : Context L α} {C : BF L α 1} {A : Formula L α}
    (s : L.Term α) (h : .all C ∈ Γ)
    (q : RawProof L (insert (C.instantiate s) Γ) A) : RawProof L Γ A :=
  ⟨.allLeft s h q.tree,
    (fun E hE => q.context_pure E (Finset.mem_insert_of_mem hE)), q.conclusion_pure⟩

end
end Lemmatheca.ProofTheory.IntuitionisticFirstOrder.EqualityFreeHarrop
