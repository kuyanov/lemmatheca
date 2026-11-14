import Lemmatheca.IntuitionisticFirstOrderDeduction.Calculus

/-! Syntactic structural operations and public wrappers for the native rules. -/
namespace Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction
open _root_.FirstOrder _root_.FirstOrder.Language
open Lemmatheca.MathematicalLogic.FirstOrderProofs
universe u v w
variable {L : Language.{u,v}} {α β γ : Type w} {c e : Bool}
noncomputable section
local instance ndStructuralFormulaEq {δ : Type w} : DecidableEq (Formula L δ) :=
  Classical.decEq _

theorem termEqual_subst (s t : L.Term α) (σ : α → L.Term β) :
    (termEqual s t).subst σ = termEqual (s.subst σ) (t.subst σ) := by
  simp [termEqual, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_equal,
    term_subst_relabel, term_relabel_subst,
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.freeScope]

theorem formula_rename_subst {n} (A : BF L α n) (f : α → β) (σ : β → L.Term γ) :
    (A.rename f).subst σ = A.subst (fun x => σ (f x)) := by
  simp only [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename,
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_comp, Term.subst]

theorem formula_subst_rename {n} (A : BF L α n) (σ : α → L.Term β) (f : β → γ) :
    (A.subst σ).rename f = A.subst (fun x => (σ x).relabel f) := by
  simp only [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename,
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_comp, term_subst_vars]

theorem liftContext_subst (Γ : Context L α) (σ : α → L.Term β) :
    (liftContext Γ).image (fun A => A.subst (liftSubst σ 1)) =
      liftContext (Γ.image (fun A => A.subst σ)) := by
  simp only [liftContext, Finset.image_image, Function.comp_def, formula_rename_subst,
    formula_subst_rename, liftSubst, Sum.elim_inl]

namespace Derivation
variable {Γ Δ : Context L α} {A B : Formula L α}

/-- Replace only the allowed contexts, retaining every logical rule. -/
def weaken (h : Derivation c e L Γ A) (hsub : Γ ⊆ Δ) : Derivation c e L Δ A := by
  clear B
  revert hsub
  induction h with
  | assumption hA => intro hsub; exact .assumption (hsub hA)
  | conjIntro _ _ ihA ihB => intro hsub; exact .conjIntro (ihA hsub) (ihB hsub)
  | conjElimLeft _ ih => intro hsub; exact .conjElimLeft (ih hsub)
  | conjElimRight _ ih => intro hsub; exact .conjElimRight (ih hsub)
  | disjIntroLeft _ ih => intro hsub; exact .disjIntroLeft (ih hsub)
  | disjIntroRight _ ih => intro hsub; exact .disjIntroRight (ih hsub)
  | disjElim _ _ _ ihAB ihA ihB =>
      intro hsub
      exact .disjElim (ihAB hsub) (ihA (Finset.insert_subset_insert _ hsub))
        (ihB (Finset.insert_subset_insert _ hsub))
  | impIntro _ ih => intro hsub; exact .impIntro (ih (Finset.insert_subset_insert _ hsub))
  | impElim _ _ ihAB ihA => intro hsub; exact .impElim (ihAB hsub) (ihA hsub)
  | negIntro _ ih => intro hsub; exact .negIntro (ih (Finset.insert_subset_insert _ hsub))
  | negElim _ _ ihA ihnA => intro hsub; exact .negElim (ihA hsub) (ihnA hsub)
  | falsumElim _ ih => intro hsub; exact .falsumElim (ih hsub)
  | classicalContradiction hc _ ih =>
      intro hsub
      exact .classicalContradiction hc (ih (Finset.insert_subset_insert _ hsub))
  | allElim t _ ih => intro hsub; exact .allElim t (ih hsub)
  | exIntro t _ ih => intro hsub; exact .exIntro t (ih hsub)
  | allIntro _ ih =>
      intro hsub
      apply Derivation.allIntro (ih (Finset.image_subset_image hsub))
  | exElim _ _ ihEx ihB =>
      intro hsub
      exact .exElim (ihEx hsub) (ihB (Finset.insert_subset_insert _
        (Finset.image_subset_image hsub)))
  | equalIntro t he => intro _; exact .equalIntro t he
  | equalElim φ s t he _ _ ihEq ihφ =>
      intro hsub
      exact .equalElim φ s t he (ihEq hsub) (ihφ hsub)

/-- Substitute the free parameters throughout the supplied tree; eigenparameters
are transported by the protected lift, rather than substituted as ambient names. -/
def substitute (h : Derivation c e L Γ A) (σ : α → L.Term β) :
    Derivation c e L (Γ.image (fun B => B.subst σ)) (A.subst σ) := by
  clear Δ B
  revert β
  induction h with
  | assumption hA => intro β σ; exact .assumption (Finset.mem_image.mpr ⟨_, hA, rfl⟩)
  | conjIntro _ _ ihA ihB =>
      intro β σ
      rw [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_conj]
      exact .conjIntro (ihA σ) (ihB σ)
  | conjElimLeft _ ih =>
      intro β σ
      exact .conjElimLeft (by simpa only [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_conj] using ih σ)
  | conjElimRight _ ih =>
      intro β σ
      exact .conjElimRight (by simpa only [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_conj] using ih σ)
  | disjIntroLeft _ ih => intro β σ; rw [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_disj]; exact .disjIntroLeft (ih σ)
  | disjIntroRight _ ih => intro β σ; rw [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_disj]; exact .disjIntroRight (ih σ)
  | disjElim _ _ _ ihAB ihA ihB =>
      intro β σ
      apply Derivation.disjElim (by simpa only [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_disj] using ihAB σ)
      · simpa only [Finset.image_insert] using ihA σ
      · simpa only [Finset.image_insert] using ihB σ
  | impIntro _ ih =>
      intro β σ
      rw [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_impl]
      apply Derivation.impIntro
      simpa only [Finset.image_insert] using ih σ
  | impElim _ _ ihAB ihA =>
      intro β σ
      exact .impElim (by simpa only [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_impl] using ihAB σ) (ihA σ)
  | negIntro _ ih =>
      intro β σ
      rw [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_neg]
      apply Derivation.negIntro
      simpa only [Finset.image_insert, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_falsum] using ih σ
  | negElim _ _ ihA ihnA =>
      intro β σ
      rw [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_falsum]
      exact .negElim (ihA σ) (by simpa only [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_neg] using ihnA σ)
  | falsumElim _ ih =>
      intro β σ
      exact .falsumElim (by simpa only [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_falsum] using ih σ)
  | classicalContradiction hc _ ih =>
      intro β σ
      apply Derivation.classicalContradiction hc
      simpa only [Finset.image_insert, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_neg, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_falsum] using ih σ
  | allElim t _ ih =>
      intro β σ
      rw [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.instantiate_subst]
      exact .allElim (t.subst σ) (by simpa only [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_all] using ih σ)
  | exIntro t _ ih =>
      intro β σ
      rw [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_ex]
      apply Derivation.exIntro (t.subst σ)
      simpa only [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.instantiate_subst] using ih σ
  | allIntro _ ih =>
      intro β σ
      rw [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_all]
      apply Derivation.allIntro
      simpa only [liftContext_subst, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.toFormula_subst] using ih (liftSubst σ 1)
  | exElim _ _ ihEx ihB =>
      intro β σ
      apply Derivation.exElim (by simpa only [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_ex] using ihEx σ)
      have hp := ihB (liftSubst σ 1)
      simp only [Finset.image_insert, liftContext_subst] at hp
      simpa only [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.toFormula_subst, formula_rename_subst, formula_subst_rename,
        liftSubst, Sum.elim_inl] using hp
  | equalIntro t he =>
      intro β σ
      rw [termEqual_subst]
      exact Derivation.equalIntro (t.subst σ) he
  | equalElim φ s t he _ _ ihEq ihφ =>
      intro β σ
      rw [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.instantiate_subst]
      exact .equalElim (φ.subst σ) (s.subst σ) (t.subst σ) he
        (by simpa only [termEqual_subst] using ihEq σ)
        (by simpa only [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.instantiate_subst] using ihφ σ)

def rename (h : Derivation c e L Γ A) (f : α → β) :
    Derivation c e L (Γ.image (fun B => B.rename f)) (A.rename f) := by
  exact h.substitute (fun x => .var (f x))

private def supplyInsert {Γ Δ : Context L α}
    (supply : ∀ B ∈ Γ, Derivation c e L Δ B) (C : Formula L α) :
    ∀ B ∈ insert C Γ, Derivation c e L (insert C Δ) B := by
  intro B hB
  by_cases he : B = C
  · subst B
    exact .assumption (Finset.mem_insert_self _ _)
  · exact (supply B ((Finset.mem_insert.mp hB).resolve_left he)).weaken
      (Finset.subset_insert _ _)

private def supplyLift {Γ Δ : Context L α}
    (supply : ∀ B ∈ Γ, Derivation c e L Δ B) :
    ∀ C ∈ liftContext Γ, Derivation c e L (liftContext Δ) C := by
  intro C hC
  have hx := Finset.mem_image.mp hC
  let B := Classical.choose hx
  have hB := Classical.choose_spec hx
  have hp := Derivation.rename (supply B hB.1) (Sum.inl : α → α ⊕ Fin 1)
  exact hB.2 ▸ hp

/-- Simultaneously replace the open assumption leaves by supplied trees. -/
def replace (h : Derivation c e L Γ A)
    (supply : ∀ B ∈ Γ, Derivation c e L Δ B) : Derivation c e L Δ A := by
  clear B
  revert supply
  induction h with
  | assumption hA => intro supply; exact supply _ hA
  | conjIntro _ _ ihA ihB => intro supply; exact .conjIntro (ihA supply) (ihB supply)
  | conjElimLeft _ ih => intro supply; exact .conjElimLeft (ih supply)
  | conjElimRight _ ih => intro supply; exact .conjElimRight (ih supply)
  | disjIntroLeft _ ih => intro supply; exact .disjIntroLeft (ih supply)
  | disjIntroRight _ ih => intro supply; exact .disjIntroRight (ih supply)
  | disjElim _ _ _ ihAB ihA ihB =>
      intro supply
      exact .disjElim (ihAB supply) (ihA (supplyInsert supply _)) (ihB (supplyInsert supply _))
  | impIntro _ ih => intro supply; exact .impIntro (ih (supplyInsert supply _))
  | impElim _ _ ihAB ihA => intro supply; exact .impElim (ihAB supply) (ihA supply)
  | negIntro _ ih => intro supply; exact .negIntro (ih (supplyInsert supply _))
  | negElim _ _ ihA ihnA => intro supply; exact .negElim (ihA supply) (ihnA supply)
  | falsumElim _ ih => intro supply; exact .falsumElim (ih supply)
  | classicalContradiction hc _ ih =>
      intro supply
      exact .classicalContradiction hc (ih (supplyInsert supply _))
  | allElim t _ ih => intro supply; exact .allElim t (ih supply)
  | exIntro t _ ih => intro supply; exact .exIntro t (ih supply)
  | allIntro _ ih => intro supply; exact .allIntro (ih (supplyLift supply))
  | exElim _ _ ihEx ihB =>
      intro supply
      exact .exElim (ihEx supply) (ihB (supplyInsert (supplyLift supply) _))
  | equalIntro t he => intro _; exact .equalIntro t he
  | equalElim D s t he _ _ ihEq ihD =>
      intro supply
      exact .equalElim D s t he (ihEq supply) (ihD supply)

/-- Composition is derived from implication introduction/elimination. -/
def cut (hA : Derivation c e L Γ A) (hB : Derivation c e L (insert A Δ) B) :
    Derivation c e L (Γ ∪ Δ) B := by
  exact .impElim ((Derivation.impIntro hB).weaken Finset.subset_union_right)
    (hA.weaken Finset.subset_union_left)

theorem deduction : Nonempty (Derivation c e L (insert A Γ) B) ↔
    Nonempty (Derivation c e L Γ (.impl A B)) := by
  constructor
  · rintro ⟨h⟩
    exact ⟨.impIntro h⟩
  · rintro ⟨h⟩
    exact ⟨.impElim (h.weaken (Finset.subset_insert _ _))
      (.assumption (Finset.mem_insert_self _ _))⟩

/-- Copy an intuitionistic tree into the classical variant. -/
def classicalize (h : Derivation false e L Γ A) : Derivation true e L Γ A := by
  clear Δ B
  induction h with
  | assumption hA => exact .assumption hA
  | conjIntro _ _ ihA ihB => exact .conjIntro ihA ihB
  | conjElimLeft _ ih => exact .conjElimLeft ih
  | conjElimRight _ ih => exact .conjElimRight ih
  | disjIntroLeft _ ih => exact .disjIntroLeft ih
  | disjIntroRight _ ih => exact .disjIntroRight ih
  | disjElim _ _ _ ihAB ihA ihB => exact .disjElim ihAB ihA ihB
  | impIntro _ ih => exact .impIntro ih
  | impElim _ _ ihAB ihA => exact .impElim ihAB ihA
  | negIntro _ ih => exact .negIntro ih
  | negElim _ _ ihA ihnA => exact .negElim ihA ihnA
  | falsumElim _ ih => exact .falsumElim ih
  | classicalContradiction hc _ _ => cases hc
  | allElim t _ ih => exact .allElim t ih
  | exIntro t _ ih => exact .exIntro t ih
  | allIntro _ ih => exact .allIntro ih
  | exElim _ _ ihEx ihB => exact .exElim ihEx ihB
  | equalIntro t he => exact .equalIntro t he
  | equalElim D s t he _ _ ihEq ihD => exact .equalElim D s t he ihEq ihD

end Derivation

namespace Proof
variable {Γ Δ : Context L α} {A B C : Formula L α}

def assumption (hA : A ∈ Γ) : Proof c e L Γ A := by
  exact Derivation.assumption (Finset.mem_image.mpr ⟨A, hA, rfl⟩)
def conjIntro (hA : Proof c e L Γ A) (hB : Proof c e L Γ B) :
    Proof c e L Γ (.conj A B) := by
  exact Derivation.conjIntro hA hB
def conjElimLeft (h : Proof c e L Γ (.conj A B)) : Proof c e L Γ A := by
  exact Derivation.conjElimLeft h
def conjElimRight (h : Proof c e L Γ (.conj A B)) : Proof c e L Γ B := by
  exact Derivation.conjElimRight h
def disjIntroLeft (h : Proof c e L Γ A) : Proof c e L Γ (.disj A B) := by
  exact Derivation.disjIntroLeft h
def disjIntroRight (h : Proof c e L Γ B) : Proof c e L Γ (.disj A B) := by
  exact Derivation.disjIntroRight h
def disjElim (h : Proof c e L Γ (.disj A B))
    (hA : Proof c e L (insert A Γ) C) (hB : Proof c e L (insert B Γ) C) :
    Proof c e L Γ C := by
  exact Derivation.disjElim (A := A.rename Sum.inl) (B := B.rename Sum.inl) h
    (by simpa only [Proof, Finset.image_insert] using hA)
    (by simpa only [Proof, Finset.image_insert] using hB)
def impIntro (h : Proof c e L (insert A Γ) B) : Proof c e L Γ (.impl A B) := by
  exact Derivation.impIntro (A := A.rename Sum.inl) (B := B.rename Sum.inl)
    (by simpa only [Proof, Finset.image_insert] using h)
def impElim (h : Proof c e L Γ (.impl A B)) (hA : Proof c e L Γ A) :
    Proof c e L Γ B := by
  exact Derivation.impElim h hA
def negIntro (h : Proof c e L (insert A Γ) .falsum) : Proof c e L Γ (.neg A) := by
  exact Derivation.negIntro (A := A.rename Sum.inl)
    (by simpa only [Proof, Finset.image_insert,
      Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename,
      Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_falsum] using h)
def negElim (h : Proof c e L Γ A) (hn : Proof c e L Γ (.neg A)) :
    Proof c e L Γ .falsum := by
  exact Derivation.negElim h hn
def falsumElim (h : Proof c e L Γ .falsum) : Proof c e L Γ A := by
  exact Derivation.falsumElim h
def classicalContradiction (h : Proof true e L (insert (.neg A) Γ) .falsum) :
    Proof true e L Γ A := by
  exact Derivation.classicalContradiction (A := A.rename Sum.inl) rfl
    (by simpa only [Proof, Finset.image_insert,
      Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename,
      Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_neg,
      Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_falsum] using h)
def allElim {D : BF L α 1} (t : L.Term α) (h : Proof c e L Γ (.all D)) :
    Proof c e L Γ (D.instantiate t) := by
  unfold Proof at h ⊢
  unfold Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename
  rw [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.instantiate_subst, term_subst_vars]
  exact Derivation.allElim (t.relabel Sum.inl)
    (by simpa only [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename,
      Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_all] using h)
def exIntro {D : BF L α 1} (t : L.Term α) (h : Proof c e L Γ (D.instantiate t)) :
    Proof c e L Γ (.ex D) := by
  unfold Proof at h ⊢
  unfold Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename
  rw [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_ex]
  apply Derivation.exIntro (t.relabel Sum.inl)
  simpa only [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename,
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.instantiate_subst, term_subst_vars] using h
def allIntro {D : BF L α 1}
    (h : Proof c e L (α := α ⊕ Fin 1) (liftContext Γ) D.toFormula) :
    Proof c e L Γ (.all D) := by
  let f : (α ⊕ Fin 1) ⊕ ℕ → (α ⊕ ℕ) ⊕ Fin 1 :=
    Sum.elim (Sum.map Sum.inl id) (fun i => .inl (.inr i))
  have hp := Derivation.rename h f
  unfold Proof
  unfold Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename
  rw [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_all]
  apply Derivation.allIntro
  have hv : liftSubst (fun x : α => (Term.var (.inl x) : L.Term (α ⊕ ℕ))) 1 =
      fun z => .var (f (.inl z)) := by
    funext z
    cases z <;> rfl
  simpa only [Proof, liftContext, Finset.image_image,
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename_comp,
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename,
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.toFormula_subst, hv,
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_comp, Term.subst,
    Function.comp_def, f, Sum.elim_inl, Sum.map_inl] using hp
def exElim {D : BF L α 1} (hEx : Proof c e L Γ (.ex D))
    (hB : Proof c e L (insert D.toFormula (liftContext Γ)) (C.rename Sum.inl)) :
    Proof c e L Γ C := by
  let f : (α ⊕ Fin 1) ⊕ ℕ → (α ⊕ ℕ) ⊕ Fin 1 :=
    Sum.elim (Sum.map Sum.inl id) (fun i => .inl (.inr i))
  have hp := Derivation.rename hB f
  unfold Proof at hEx ⊢
  apply Derivation.exElim (B := D.subst (fun x => .var (.inl x)))
    (by simpa only [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename,
      Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_ex] using hEx)
  have hv : liftSubst (fun x : α => (Term.var (.inl x) : L.Term (α ⊕ ℕ))) 1 =
      fun z => .var (f (.inl z)) := by
    funext z
    cases z <;> rfl
  simpa only [Proof, liftContext, Finset.image_insert, Finset.image_image,
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename_comp,
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename,
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.toFormula_subst, hv,
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_comp, Term.subst,
    Function.comp_def, f, Sum.elim_inl, Sum.map_inl] using hp
def equalIntro (t : L.Term α) : Proof c true L Γ (termEqual t t) := by
  unfold Proof
  unfold Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename
  rw [termEqual_subst, term_subst_vars]
  exact Derivation.equalIntro (t.relabel Sum.inl) rfl
def equalElim (D : BF L α 1) (s t : L.Term α)
    (he : Proof c true L Γ (termEqual s t)) (hD : Proof c true L Γ (D.instantiate s)) :
    Proof c true L Γ (D.instantiate t) := by
  unfold Proof at he hD ⊢
  unfold Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename
  rw [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.instantiate_subst, term_subst_vars]
  exact Derivation.equalElim (D.subst (fun x => .var (.inl x))) (s.relabel Sum.inl) (t.relabel Sum.inl) rfl
    (by simpa only [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename,
      termEqual_subst, term_subst_vars] using he)
    (by simpa only [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename,
      Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.instantiate_subst, term_subst_vars] using hD)

def weaken (h : Proof c e L Γ A) (hsub : Γ ⊆ Δ) : Proof c e L Δ A := by
  exact Derivation.weaken h (Finset.image_subset_image hsub)
def substitute (h : Proof c e L Γ A) (σ : α → L.Term β) :
    Proof c e L (Γ.image (fun B => B.subst σ)) (A.subst σ) := by
  let τ : α ⊕ ℕ → L.Term (β ⊕ ℕ) :=
    Sum.elim (fun x => (σ x).relabel Sum.inl) (fun i => .var (.inr i))
  have hp := Derivation.substitute h τ
  simpa only [Proof, Finset.image_image, Function.comp_def, formula_rename_subst,
    formula_subst_rename, τ, Sum.elim_inl] using hp
def rename (h : Proof c e L Γ A) (f : α → β) :
    Proof c e L (Γ.image (fun B => B.rename f)) (A.rename f) := by
  exact h.substitute (fun x => .var (f x))
def replace (h : Proof c e L Γ A) (supply : ∀ B ∈ Γ, Proof c e L Δ B) :
    Proof c e L Δ A := by
  apply Derivation.replace h
  intro C hC
  have hx := Finset.mem_image.mp hC
  let B := Classical.choose hx
  have hB := Classical.choose_spec hx
  exact hB.2 ▸ supply B hB.1
def cut (hA : Proof c e L Γ A) (hB : Proof c e L (insert A Δ) B) :
    Proof c e L (Γ ∪ Δ) B := by
  exact impElim ((impIntro hB).weaken Finset.subset_union_right)
    (hA.weaken Finset.subset_union_left)
theorem deduction : Derives c e L (insert A Γ) B ↔ Derives c e L Γ (.impl A B) := by
  constructor
  · rintro ⟨h⟩
    exact ⟨impIntro h⟩
  · rintro ⟨h⟩
    exact ⟨impElim (h.weaken (Finset.subset_insert _ _))
      (assumption (Finset.mem_insert_self _ _))⟩
def classicalize (h : Proof false e L Γ A) : Proof true e L Γ A := by
  exact Derivation.classicalize h

end Proof

namespace TheoryProof
variable {T S : Set (Formula L α)} {A : Formula L α}

def ofFinite {Γ : Context L α} (hΓ : ∀ B ∈ Γ, B ∈ T) (h : Proof c e L Γ A) :
    TheoryProof c e L T A := ⟨Γ, hΓ, h⟩

/-- Finitely many supplied supports are unioned before proof replacement. -/
def replace (h : TheoryProof c e L T A) (supply : ∀ B ∈ T, TheoryProof c e L S B) :
    TheoryProof c e L S A := by
  let Δ : Context L α := h.assumptions.attach.biUnion
    (fun B => (supply B.1 (h.allowed B.1 B.2)).assumptions)
  refine ⟨Δ, ?_, ?_⟩
  · intro C hC
    rcases Finset.mem_biUnion.mp hC with ⟨B, _, hCB⟩
    exact (supply B.1 (h.allowed B.1 B.2)).allowed C hCB
  · apply h.derivation.replace
    intro B hB
    apply (supply B (h.allowed B hB)).derivation.weaken
    intro C hC
    exact Finset.mem_biUnion.mpr ⟨⟨B, hB⟩, Finset.mem_attach _ _, hC⟩

end TheoryProof

theorem theory_finite_support {T : Set (Formula L α)} {A : Formula L α} :
    TheoryDerives c e L T A ↔ ∃ Γ : Context L α,
      (∀ B ∈ Γ, B ∈ T) ∧ Derives c e L Γ A := by
  constructor
  · rintro ⟨h⟩
    exact ⟨h.assumptions, h.allowed, ⟨h.derivation⟩⟩
  · rintro ⟨Γ, hΓ, ⟨hp⟩⟩
    exact ⟨⟨Γ, hΓ, hp⟩⟩

theorem theory_finset {Γ : Context L α} {A : Formula L α} :
    TheoryDerives c e L (↑Γ : Set (Formula L α)) A ↔ Derives c e L Γ A := by
  constructor
  · rintro ⟨h⟩
    exact ⟨h.derivation.weaken h.allowed⟩
  · rintro ⟨h⟩
    exact ⟨⟨Γ, fun _ hB => hB, h⟩⟩

theorem theory_trans {T S : Set (Formula L α)} {A : Formula L α}
    (h : TheoryDerives c e L T A) (supply : ∀ B ∈ T, TheoryDerives c e L S B) :
    TheoryDerives c e L S A := by
  classical
  rcases h with ⟨h⟩
  exact ⟨h.replace (fun B hB => Classical.choice (supply B hB))⟩

end
end Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction
