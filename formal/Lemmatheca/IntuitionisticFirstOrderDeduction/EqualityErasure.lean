import Lemmatheca.IntuitionisticFirstOrderDeduction.Structural

/-! Purification of equality-disabled trees, without claiming conservativity for
trees that use logical equality rules. -/
namespace Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction
open _root_.FirstOrder _root_.FirstOrder.Language
universe u v w
variable {L : Language.{u,v}} {α β : Type w} {c : Bool}
noncomputable section
local instance ndErasureFormulaEq {δ : Type w} : DecidableEq (Formula L δ) :=
  Classical.decEq _

/-- Replace equality atoms by falsum, retaining every other full constructor. -/
def eraseEquality : ∀ {n}, BF L α n → BF L α n
  | _, .falsum | _, .equal _ _ => .falsum
  | _, .rel R ts => .rel R ts
  | _, .neg A => .neg (eraseEquality A)
  | _, .conj A B => .conj (eraseEquality A) (eraseEquality B)
  | _, .disj A B => .disj (eraseEquality A) (eraseEquality B)
  | _, .impl A B => .impl (eraseEquality A) (eraseEquality B)
  | _, .all A => .all (eraseEquality A)
  | _, .ex A => .ex (eraseEquality A)

def eraseContext (Γ : Context L α) : Context L α := Γ.image eraseEquality

def ContextPure (Γ : Context L α) : Prop := ∀ A ∈ Γ, A.EqualityFree

/-- Every context and conclusion displayed anywhere in this actual tree is
equality-free; equality rules are disabled at the type level. -/
def Derivation.Pure : ∀ {α : Type w} {Γ : Context L α} {A : Formula L α},
    Derivation c false L Γ A → Prop
  | _, Γ, A, h => ContextPure Γ ∧ A.EqualityFree ∧ match h with
    | .assumption _ | .equalIntro _ _ => True
    | .conjIntro p q | .impElim p q | .negElim p q | .exElim p q => p.Pure ∧ q.Pure
    | .conjElimLeft p | .conjElimRight p | .disjIntroLeft p | .disjIntroRight p
      | .impIntro p | .negIntro p | .falsumElim p | .classicalContradiction _ p
      | .allElim _ p | .exIntro _ p | .allIntro p => p.Pure
    | .disjElim p q r => p.Pure ∧ q.Pure ∧ r.Pure
    | .equalElim _ _ _ _ p q => p.Pure ∧ q.Pure

def Proof.Pure {Γ : Context L α} {A : Formula L α} (h : Proof c false L Γ A) : Prop :=
  Derivation.Pure h

theorem eraseEquality_map {n m} (A : BF L α n) (σ : ScopeSubst L α β n m) :
    eraseEquality (A.map σ) = (eraseEquality A).map σ := by
  induction A generalizing m <;> simp_all [eraseEquality, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.map]

theorem eraseEquality_subst {n} (A : BF L α n) (σ : α → L.Term β) :
    eraseEquality (A.subst σ) = (eraseEquality A).subst σ := by
  exact eraseEquality_map A (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.freeScope σ n)

theorem eraseEquality_rename {n} (A : BF L α n) (f : α → β) :
    eraseEquality (A.rename f) = (eraseEquality A).rename f := by
  exact eraseEquality_subst A (fun x => .var (f x))

theorem eraseEquality_open {n} (A : BF L α n) :
    eraseEquality A.toFormula = (eraseEquality A).toFormula := by
  exact eraseEquality_map A _

theorem eraseEquality_instantiate (A : BF L α 1) (t : L.Term α) :
    eraseEquality (A.instantiate t) = (eraseEquality A).instantiate t := by
  exact eraseEquality_map A _

theorem eraseEquality_pure {n} (A : BF L α n) : (eraseEquality A).EqualityFree := by
  induction A <;> simp_all [eraseEquality, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.EqualityFree]

theorem eraseEquality_eq {n} (A : BF L α n) (h : A.EqualityFree) :
    eraseEquality A = A := by
  induction A <;> simp_all [eraseEquality, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.EqualityFree]

private theorem eraseContext_pure (Γ : Context L α) : ContextPure (eraseContext Γ) := by
  intro A hA
  rcases Finset.mem_image.mp hA with ⟨B, _, rfl⟩
  exact eraseEquality_pure B

private theorem eraseContext_lift (Γ : Context L α) :
    eraseContext (liftContext Γ) = liftContext (eraseContext Γ) := by
  simp only [eraseContext, liftContext, Finset.image_image, Function.comp_def,
    eraseEquality_rename]

private theorem eraseContext_eq (Γ : Context L α) (hΓ : ContextPure Γ) :
    eraseContext Γ = Γ := by
  ext A
  constructor
  · intro hA
    rcases Finset.mem_image.mp hA with ⟨B, hB, he⟩
    rw [eraseEquality_eq B (hΓ B hB)] at he
    exact he ▸ hB
  · intro hA
    exact Finset.mem_image.mpr ⟨A, hA, eraseEquality_eq A (hΓ A hA)⟩

private theorem eraseContext_insert (Γ : Context L α) (A : Formula L α) :
    eraseContext (insert A Γ) = insert (eraseEquality A) (eraseContext Γ) := by
  simp only [eraseContext, Finset.image_insert]

private def eraseWithPurity {Γ : Context L α} {A : Formula L α}
    (h : Derivation c false L Γ A) :
    {p : Derivation c false L (eraseContext Γ) (eraseEquality A) // p.Pure} := by
  induction h with
  | assumption hA =>
      exact ⟨.assumption (Finset.mem_image.mpr ⟨_, hA, rfl⟩),
        eraseContext_pure _, eraseEquality_pure _, trivial⟩
  | conjIntro _ _ ihA ihB =>
      exact ⟨.conjIntro ihA.1 ihB.1,
        eraseContext_pure _, eraseEquality_pure _, ihA.2, ihB.2⟩
  | conjElimLeft _ ih =>
      exact ⟨.conjElimLeft ih.1, eraseContext_pure _, eraseEquality_pure _, ih.2⟩
  | conjElimRight _ ih =>
      exact ⟨.conjElimRight ih.1, eraseContext_pure _, eraseEquality_pure _, ih.2⟩
  | disjIntroLeft _ ih =>
      exact ⟨.disjIntroLeft ih.1, eraseContext_pure _, eraseEquality_pure _, ih.2⟩
  | disjIntroRight _ ih =>
      exact ⟨.disjIntroRight ih.1, eraseContext_pure _, eraseEquality_pure _, ih.2⟩
  | disjElim _ _ _ ihAB ihA ihB =>
      rw [eraseContext_insert] at ihA ihB
      exact ⟨.disjElim ihAB.1 ihA.1 ihB.1,
        eraseContext_pure _, eraseEquality_pure _, ihAB.2, ihA.2, ihB.2⟩
  | impIntro _ ih =>
      rw [eraseContext_insert] at ih
      exact ⟨.impIntro ih.1, eraseContext_pure _, eraseEquality_pure _, ih.2⟩
  | impElim _ _ ihAB ihA =>
      exact ⟨.impElim ihAB.1 ihA.1,
        eraseContext_pure _, eraseEquality_pure _, ihAB.2, ihA.2⟩
  | negIntro _ ih =>
      rw [eraseContext_insert] at ih
      exact ⟨.negIntro ih.1, eraseContext_pure _, eraseEquality_pure _, ih.2⟩
  | negElim _ _ ihA ihnA =>
      exact ⟨.negElim ihA.1 ihnA.1,
        eraseContext_pure _, eraseEquality_pure _, ihA.2, ihnA.2⟩
  | falsumElim _ ih =>
      exact ⟨.falsumElim ih.1, eraseContext_pure _, eraseEquality_pure _, ih.2⟩
  | classicalContradiction hc _ ih =>
      rw [eraseContext_insert] at ih
      exact ⟨.classicalContradiction hc ih.1,
        eraseContext_pure _, eraseEquality_pure _, ih.2⟩
  | @allElim α Γ B t _ ih =>
      rw [eraseEquality_instantiate]
      refine ⟨.allElim t ih.1, eraseContext_pure _, ?_, ih.2⟩
      simpa only [eraseEquality_instantiate] using eraseEquality_pure (B.instantiate t)
  | exIntro t _ ih =>
      rw [eraseEquality_instantiate] at ih
      exact ⟨.exIntro t ih.1, eraseContext_pure _, eraseEquality_pure _, ih.2⟩
  | allIntro _ ih =>
      rw [eraseContext_lift, eraseEquality_open] at ih
      exact ⟨.allIntro ih.1, eraseContext_pure _, eraseEquality_pure _, ih.2⟩
  | exElim _ _ ihEx ihB =>
      rw [eraseContext_insert, eraseContext_lift, eraseEquality_open,
        eraseEquality_rename] at ihB
      exact ⟨.exElim ihEx.1 ihB.1,
        eraseContext_pure _, eraseEquality_pure _, ihEx.2, ihB.2⟩
  | equalIntro _ he => cases he
  | equalElim _ _ _ he _ _ _ _ => cases he

namespace Derivation
variable {Γ : Context L α} {A : Formula L α}

/-- Reapply each equality-disabled rule to its erased premises. -/
def erase (h : Derivation c false L Γ A) :
    Derivation c false L (eraseContext Γ) (eraseEquality A) := by
  exact (eraseWithPurity h).1

theorem erase_pure (h : Derivation c false L Γ A) : h.erase.Pure := by
  exact (eraseWithPurity h).2

/-- Equalities in intermediate formulas may be erased while fixing pure endpoints. -/
def purify (h : Derivation c false L Γ A) (hΓ : ContextPure Γ) (hA : A.EqualityFree) :
    {p : Derivation c false L Γ A // p.Pure} := by
  have hp := eraseWithPurity h
  rw [eraseContext_eq Γ hΓ, eraseEquality_eq A hA] at hp
  exact hp

end Derivation

private def erasePublicWithPurity {Γ : Context L α} {A : Formula L α}
    (h : Proof c false L Γ A) :
    {p : Proof c false L (eraseContext Γ) (eraseEquality A) // p.Pure} := by
  have hp := eraseWithPurity h
  have hc : eraseContext (Γ.image (fun B => B.rename (Sum.inl : α → α ⊕ ℕ))) =
      (eraseContext Γ).image (fun B => B.rename Sum.inl) := by
    simp only [eraseContext, Finset.image_image, Function.comp_def, eraseEquality_rename]
  rw [hc, eraseEquality_rename] at hp
  exact hp

namespace Proof
variable {Γ : Context L α} {A : Formula L α}

def erase (h : Proof c false L Γ A) :
    Proof c false L (eraseContext Γ) (eraseEquality A) := by
  exact (erasePublicWithPurity h).1

theorem erase_pure (h : Proof c false L Γ A) : h.erase.Pure := by
  exact (erasePublicWithPurity h).2

def purify (h : Proof c false L Γ A) (hΓ : ContextPure Γ) (hA : A.EqualityFree) :
    {p : Proof c false L Γ A // p.Pure} := by
  have hp := erasePublicWithPurity h
  rw [eraseContext_eq Γ hΓ, eraseEquality_eq A hA] at hp
  exact hp

end Proof
end
end Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction
