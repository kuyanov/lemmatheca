import Lemmatheca.FirstOrderFriedmanTranslation.Proofs

namespace Lemmatheca.ProofTheory.FirstOrder.FriedmanTranslation
open _root_.FirstOrder _root_.FirstOrder.Language
universe u v a
variable {L : Language.{u,v}} {α : Type a} {e : Bool}

noncomputable section
local instance friedmanPublicFormulaEq {δ : Type*} : DecidableEq (Formula L δ) :=
  Classical.decEq _

variable {Γ : NaturalDeduction.Context L α} {A : Formula L α}

/-- Apply the raw map to the very same countably reserved input tree, using u₀.
Only the exact context/formula renaming identities transport its endpoints. -/
def translatePublic (R : Formula L α) (p : NaturalDeduction.Proof false e L Γ A) :
    NaturalDeduction.Proof false e L (context R Γ) (formula R A) := by
  unfold NaturalDeduction.Proof at p ⊢
  have hp := translate (R.rename (Sum.inl : α → α ⊕ ℕ)) (.var (.inr (0 : ℕ))) p
  simpa only [context_rename, ← formula_rename] using hp

/-- Image the actual given finite support, then translate its actual proof field. -/
def translateTheory (R : Formula L α) {T : Set (Formula L α)}
    (p : NaturalDeduction.TheoryProof false e L T A) :
    NaturalDeduction.TheoryProof false e L (theory R T) (formula R A) := by
  refine ⟨context R p.assumptions, ?_, translatePublic R p.derivation⟩
  intro D hD
  rcases Finset.mem_image.mp hD with ⟨C, hC, rfl⟩
  exact Set.mem_image_of_mem _ (p.allowed C hC)

theorem translateTheory_support (R : Formula L α) {T : Set (Formula L α)}
    (p : NaturalDeduction.TheoryProof false e L T A) :
    (translateTheory R p).assumptions = context R p.assumptions := by
  rfl

theorem translateTheory_proof (R : Formula L α) {T : Set (Formula L α)}
    (p : NaturalDeduction.TheoryProof false e L T A) :
    (translateTheory R p).derivation = translatePublic R p.derivation := by
  rfl

/-- Restrict the same image proof to its actual finite allowed theory before
replacement. Choice selects a preimage only from the original finite support;
its supplied certificate is retained and existing replacement unions supports. -/
def translateTheoryUnder (R : Formula L α) {T S : Set (Formula L α)}
    (p : NaturalDeduction.TheoryProof false e L T A)
    (supply : ∀ C ∈ T, NaturalDeduction.TheoryProof false e L S (formula R C)) :
    NaturalDeduction.TheoryProof false e L S (formula R A) := by
  let finiteImage : NaturalDeduction.TheoryProof false e L
      (context R p.assumptions : Set (Formula L α)) (formula R A) :=
    ⟨context R p.assumptions, (fun _ h => h), (translateTheory R p).derivation⟩
  apply finiteImage.replace
  intro D hD
  have hmem : D ∈ context R p.assumptions := hD
  have hex : ∃ C, C ∈ p.assumptions ∧ formula R C = D := Finset.mem_image.mp hmem
  let C := Classical.choose hex
  have hC : C ∈ p.assumptions ∧ formula R C = D := Classical.choose_spec hex
  exact hC.2 ▸ supply C (p.allowed C hC.1)

theorem public_preservation (R : Formula L α) :
    NaturalDeduction.Derives false e L Γ A →
      NaturalDeduction.Derives false e L (context R Γ) (formula R A) := by
  rintro ⟨p⟩
  exact ⟨translatePublic R p⟩

theorem theory_preservation (R : Formula L α) (T : Set (Formula L α)) :
    NaturalDeduction.TheoryDerives false e L T A →
      NaturalDeduction.TheoryDerives false e L (theory R T) (formula R A) := by
  rintro ⟨p⟩
  exact ⟨translateTheory R p⟩

end
end Lemmatheca.ProofTheory.FirstOrder.FriedmanTranslation
