import Lemmatheca.EqualityFreeIntuitionisticFirstOrderSequents.Calculus

/-! Harrop form includes the equality-free restriction at every scoped node. -/
namespace Lemmatheca.ProofTheory.IntuitionisticFirstOrder.EqualityFreeHarrop
open _root_.FirstOrder _root_.FirstOrder.Language
universe u v w w'
variable {L : Language.{u,v}} {α : Type w} {β : Type w'}
noncomputable section
local instance ifohSyntaxEq {δ : Type*} : DecidableEq (Formula L δ) := Classical.decEq _

/-- Inputs and negation arguments are arbitrary equality-free formulas. -/
def IsHarrop : {n : ℕ} → BF L α n → Prop
  | _, .falsum | _, .rel _ _ => True
  | _, .equal _ _ | _, .disj _ _ | _, .ex _ => False
  | _, .neg A => A.EqualityFree
  | _, .conj A B => IsHarrop A ∧ IsHarrop B
  | _, .impl A B => A.EqualityFree ∧ IsHarrop B
  | _, .all A => IsHarrop A

def ContextHarrop (Γ : Context L α) : Prop := ∀ D ∈ Γ, IsHarrop D

/-- Consistency in this exact raw name universe, without adding any reserve. -/
def Consistent (Γ : Context L α) : Prop := ¬ Nonempty (RawProof L Γ .falsum)

theorem harrop_pure {n} {A : BF L α n} (hA : IsHarrop A) : A.EqualityFree := by
  induction A <;> simp_all [IsHarrop, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.EqualityFree]

theorem harrop_map {n m} {A : BF L α n} (hA : IsHarrop A)
    (σ : Lemmatheca.ProofTheory.FirstOrder.ScopeSubst L α β n m) :
    IsHarrop (A.map σ) := by
  induction A generalizing m <;>
    simp_all [IsHarrop, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.map]

theorem context_pure {Γ : Context L α} (hΓ : ContextHarrop Γ) : ContextPure Γ := by
  intro D hD
  exact harrop_pure (hΓ D hD)

theorem context_subst {Γ : Context L α} (hΓ : ContextHarrop Γ) (σ : α → L.Term β) :
    ContextHarrop (Γ.image (fun D => D.subst σ)) := by
  intro D hD
  obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hD
  exact harrop_map (hΓ C hC) _

theorem context_rename {Γ : Context L α} (hΓ : ContextHarrop Γ) (f : α → β) :
    ContextHarrop (Γ.image (fun D => D.rename f)) := by
  exact context_subst hΓ (fun x => .var (f x))

theorem context_conjunction {Γ : Context L α} {C D : Formula L α}
    (hΓ : ContextHarrop Γ) (h : .conj C D ∈ Γ) :
    ContextHarrop (insert C (insert D Γ)) := by
  intro E hE
  simp only [Finset.mem_insert] at hE
  rcases hE with rfl | rfl | hE
  · exact (hΓ _ h).1
  · exact (hΓ _ h).2
  · exact hΓ E hE

theorem context_implication {Γ : Context L α} {C D : Formula L α}
    (hΓ : ContextHarrop Γ) (h : .impl C D ∈ Γ) :
    ContextHarrop (insert D Γ) := by
  intro E hE
  rcases Finset.mem_insert.mp hE with rfl | hE
  · exact (hΓ _ h).2
  · exact hΓ E hE

theorem context_universal {Γ : Context L α} {C : BF L α 1}
    (hΓ : ContextHarrop Γ) (h : .all C ∈ Γ) (s : L.Term α) :
    ContextHarrop (insert (C.instantiate s) Γ) := by
  intro E hE
  rcases Finset.mem_insert.mp hE with rfl | hE
  · exact harrop_map (A := C) (hΓ _ h) _
  · exact hΓ E hE

theorem context_no_disjunction {Γ : Context L α} (hΓ : ContextHarrop Γ)
    (A B : Formula L α) : .disj A B ∉ Γ := by
  intro h
  exact hΓ _ h

theorem context_no_existential {Γ : Context L α} (hΓ : ContextHarrop Γ)
    (B : BF L α 1) : .ex B ∉ Γ := by
  intro h
  exact hΓ _ h

end
end Lemmatheca.ProofTheory.IntuitionisticFirstOrder.EqualityFreeHarrop
