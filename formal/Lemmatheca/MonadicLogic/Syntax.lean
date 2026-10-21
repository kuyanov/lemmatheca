import Lemmatheca.ExistentialUniversalSentences.FiniteModels

/-! Actual shared first-order syntax for finite constant-free unary languages. -/
namespace Lemmatheca.MathematicalLogic.MonadicLogic
open FirstOrder FirstOrder.Language Structure

abbrev arities (k : ℕ) : List ℕ := List.replicate k 1
abbrev lang (k : ℕ) : Language := ExistentialUniversalSentences.lang 0 (arities k)
abbrev Profile (k : ℕ) := Fin k → Bool

def predicate (k : ℕ) (i : Fin k) : (lang k).Relations 1 :=
  ⟨⟨i.val, by simp [arities]⟩, by simp [arities]⟩

/-- Interpret any supplied family of unary predicates in the finite shared language. -/
@[instance_reducible]
def structureOfPredicates {k : ℕ} {M : Type*} (P : Fin k → M → Prop) : (lang k).Structure M where
  funMap := fun f _ => match f with | .constant i => i.elim0
  RelMap := fun {n} r a => P ⟨r.val.val, by simpa [arities] using r.val.isLt⟩
    (a ⟨0, by
      have h : 1 = n := by simpa [arities] using r.property
      omega⟩)

noncomputable def profile {k : ℕ} {M : Type*} [(lang k).Structure M] (a : M) : Profile k :=
  fun i => @decide (RelMap (L := lang k) (predicate k i) (fun _ => a)) (Classical.propDecidable _)

def profileClass {k : ℕ} {M : Type*} [(lang k).Structure M] (p : Profile k) : Set M :=
  {x | profile x = p}

def quantifiers {k : ℕ} : {n : ℕ} → (lang k).BoundedFormula Empty n → ℕ
  | _, .falsum => 0
  | _, .equal _ _ => 0
  | _, .rel _ _ => 0
  | _, .imp φ ψ => quantifiers φ + quantifiers ψ
  | _, .all φ => quantifiers φ + 1

section Capacity
variable {M N P : Type*}

/-- A finite subset of exactly the requested size, all of one profile. -/
def AtLeast (r : ℕ) (π : M → P) (p : P) : Prop :=
  ∃ A : Finset M, A.card = r ∧ ∀ x ∈ A, π x = p

/-- Equal small finite fibres, or at least the cap on both sides. -/
def Capacities (r : ℕ) (π : M → P) (ρ : N → P) : Prop :=
  ∀ p, (∃ (A : Finset M) (B : Finset N),
    (∀ x, π x = p ↔ x ∈ A) ∧ (∀ y, ρ y = p ↔ y ∈ B) ∧
      A.card = B.card ∧ A.card < r) ∨ (AtLeast r π p ∧ AtLeast r ρ p)

/-- The equality pattern and the profile of every assigned point are preserved. -/
def Matching (π : M → P) (ρ : N → P) {n : ℕ} (a : Fin n → M) (b : Fin n → N) : Prop :=
  (∀ i, π (a i) = ρ (b i)) ∧ ∀ i j, a i = a j ↔ b i = b j

end Capacity

theorem quantifiers_not {k n : ℕ} (φ : (lang k).BoundedFormula Empty n) :
    quantifiers φ.not = quantifiers φ := by rfl

theorem quantifiers_ex {k n : ℕ} (φ : (lang k).BoundedFormula Empty (n+1)) :
    quantifiers φ.ex = quantifiers φ + 1 := by rfl

end Lemmatheca.MathematicalLogic.MonadicLogic
